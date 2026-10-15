"""Selectable provider configurations for a single interactive proof session."""
from copy import deepcopy
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROVIDERS = ("openai", "anthropic", "google")
KEY_ENV = {"openai": "OPENAI_API_KEY", "anthropic": "ANTHROPIC_API_KEY", "google": "GEMINI_API_KEY"}


def available_models(path=None):
    data = json.loads(Path(path or ROOT / "environment/models.json").read_text())
    models = data["models"]
    if len({m["id"] for m in models}) != len(models):
        raise ValueError("Model IDs in the registry must be unique")
    for model in models:
        if model["provider"] not in PROVIDERS or not isinstance(model["id"], str):
            raise ValueError("Invalid provider/model in registry")
        if type(model["max_output"]) is not int or model["max_output"] < 1:
            raise ValueError("Model output allowance must be a positive integer")
    return models


def resolve_model(model_id, provider=None, *, registry=None, effort=None, thinking=None, max_output=None):
    models = available_models(registry)
    match = next((m for m in models if m["id"] == model_id), None)
    if match:
        config = deepcopy(match)
        if provider and config["provider"] != provider:
            raise ValueError("Selected provider does not match the registered model")
    else:
        if provider is None:
            raise ValueError("For an unlisted model, supply --provider openai, anthropic or google")
        config = dict(id=model_id, label=model_id, provider=provider, max_output=16000, effort=None)
        if provider == "anthropic":
            config["thinking"] = "off"
    if effort is not None:
        config["effort"] = None if effort == "none" else effort
    if thinking is not None:
        if config["provider"] != "anthropic":
            raise ValueError("--thinking applies to Anthropic models")
        config["thinking"] = thinking
    if max_output is not None:
        if match and max_output > match["max_output"]:
            raise ValueError("--max-output exceeds this model's configured output limit")
        config["max_output"] = max_output
    if config["provider"] == "google" and config.get("effort") not in (None, "low", "medium", "high"):
        raise ValueError("Google thinking level must be low, medium or high")
    if config["provider"] == "anthropic" and config.get("thinking") == "off" and config.get("effort"):
        raise ValueError("For Anthropic, an effort override needs manual or adaptive thinking")
    if config.get("thinking") == "manual":
        if config["max_output"] <= 1024:
            raise ValueError("Manual thinking needs --max-output greater than 1024")
        config["thinking_budget"] = min(config.get("thinking_budget", 10000), config["max_output"] - 1)
    return config
