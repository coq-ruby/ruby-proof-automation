"""Provider requests and conversation history for a selected proof session.

SDKs are imported only for the selected provider. Native signed assistant blocks
are retained for Anthropic/Google; OpenAI uses visible-text conversation history.
Calls are recorded before sending and responses before interpretation. Credentials
never form part of a request log. Uncertain transport requests are not retried.
"""
from copy import deepcopy
import json
from pathlib import Path
import time


class ProviderStop(RuntimeError):
    pass


def message_key(messages):
    return tuple((m["role"], m["content"]) for m in messages)


def as_dict(value):
    return value if isinstance(value, dict) else value.model_dump(mode="json", exclude_none=True)


class ProviderCalls:
    def __init__(self, config, key, directory, *, timeout=600, max_calls=0, client=None):
        self.config, self.directory = deepcopy(config), Path(directory)
        self.timeout, self.max_calls = timeout, max_calls
        self.count, self.native = 0, {}
        self.last_usage = None
        self.client = client if client is not None else self.create_client(key)

    def create_client(self, key):
        provider = self.config["provider"]
        if provider == "openai":
            from openai import OpenAI
            return OpenAI(api_key=key, max_retries=0, timeout=self.timeout)
        if provider == "anthropic":
            from anthropic import Anthropic
            return Anthropic(api_key=key, max_retries=0, timeout=self.timeout)
        from google import genai
        from google.genai import types
        return genai.Client(api_key=key, http_options=types.HttpOptions(
            timeout=int(self.timeout * 1000), retry_options=types.HttpRetryOptions(attempts=1)))

    def native_messages(self, messages):
        provider = self.config["provider"]
        result = []
        for index, message in enumerate(messages):
            native = self.native.get(message_key(messages[:index + 1]))
            if provider == "google":
                role = "model" if message["role"] == "assistant" else "user"
                result.append(deepcopy(native) if native else dict(role=role, parts=[dict(text=message["content"])]))
            else:
                result.append(dict(role=message["role"], content=deepcopy(native) if native else message["content"]))
        return result

    def request(self, system, messages, temperature):
        cfg = self.config
        provider = cfg["provider"]
        if provider == "openai":
            request = dict(model=cfg["id"], instructions=system, input=deepcopy(messages),
                           max_output_tokens=cfg["max_output"], store=False)
            if cfg.get("effort"):
                request["reasoning"] = dict(effort=cfg["effort"])
            return request
        if provider == "anthropic":
            request = dict(model=cfg["id"], system=system, messages=self.native_messages(messages),
                           max_tokens=cfg["max_output"])
            thinking = cfg.get("thinking", "off")
            if thinking == "off":
                request["temperature"] = temperature
            else:
                request["thinking"] = (dict(type="adaptive") if thinking == "adaptive" else
                                       dict(type="enabled", budget_tokens=cfg["thinking_budget"]))
                if cfg.get("effort"):
                    request["output_config"] = dict(effort=cfg["effort"])
            return request
        config = dict(system_instruction=system, temperature=1.0, max_output_tokens=cfg["max_output"])
        if cfg.get("effort"):
            config["thinking_config"] = dict(thinking_level=cfg["effort"].upper(), include_thoughts=False)
        return dict(model=cfg["id"], contents=self.native_messages(messages), config=config)

    def decode(self, raw):
        provider = self.config["provider"]
        if provider == "openai":
            if raw.get("status") != "completed":
                raise ProviderStop("OpenAI response incomplete; increase the output allowance or inspect the saved response")
            parts = [content for item in raw.get("output", []) if item.get("type") == "message"
                     for content in item.get("content", [])]
            if any(part.get("type") == "refusal" for part in parts):
                raise ProviderStop("The provider refused this request")
            text = "\n".join(part["text"] for part in parts if part.get("type") == "output_text")
            usage = raw.get("usage")
            native = None
        elif provider == "anthropic":
            reason = raw.get("stop_reason")
            if reason == "refusal":
                raise ProviderStop("The provider refused this request")
            if reason != "end_turn":
                raise ProviderStop(f"Anthropic stopped with {reason}; response saved without applying partial output")
            native = raw.get("content", [])
            if any(part.get("type") not in ("text", "thinking", "redacted_thinking") for part in native):
                raise ProviderStop("Unexpected non-text provider action")
            text = "\n".join(part["text"] for part in native if part.get("type") == "text")
            usage = raw.get("usage")
        else:
            candidates = raw.get("candidates", [])
            if len(candidates) != 1 or candidates[0].get("finish_reason") != "STOP":
                reason = ", ".join(c.get("finish_reason", "UNKNOWN") for c in candidates) or "no candidate"
                raise ProviderStop(f"Google stopped with {reason}; response saved without applying partial output")
            native = candidates[0].get("content", {})
            parts = native.get("parts", [])
            if any(part.get("function_call") for part in parts):
                raise ProviderStop("Unexpected provider tool call")
            text = "".join(part.get("text", "") for part in parts if not part.get("thought"))
            usage = raw.get("usage_metadata")
        if not text.strip():
            raise ProviderStop("No visible proof text in the saved response")
        return text.strip(), native, usage

    def invoke(self, system, messages, temperature, label):
        if self.max_calls and self.count >= self.max_calls:
            raise ProviderStop("The configured per-session request limit was reached")
        request = self.request(system, messages, temperature)
        self.count += 1
        file = self.directory / f"api_{self.count:04d}.json"
        record = dict(label=label, request=request, status="dispatching")
        file.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
        started = time.monotonic()
        print(f"\n  Request {self.count}: {self.config['id']} [{label}]", flush=True)
        try:
            provider = self.config["provider"]
            if provider == "openai":
                response = self.client.responses.create(**request)
            elif provider == "anthropic":
                with self.client.messages.stream(**request) as stream:
                    response = stream.get_final_message()
            else:
                from google.genai import types
                response = self.client.models.generate_content(model=request["model"], contents=request["contents"],
                    config=types.GenerateContentConfig(**request["config"]))
            raw = as_dict(response)
        except Exception as error:
            record.update(status="transport_error", error_type=type(error).__name__, seconds=time.monotonic() - started)
            file.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
            raise ProviderStop(f"{type(error).__name__} during the provider request; no automatic resend") from error
        record.update(status="received", response=raw, seconds=time.monotonic() - started)
        file.write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n")
        text, native, self.last_usage = self.decode(raw)
        if native:
            self.native[message_key(messages + [dict(role="assistant", content=text)])] = deepcopy(native)
        return text

    def close(self):
        close = getattr(self.client, "close", None)
        if close:
            close()
