#!/usr/bin/env python3
"""Select one model and one benchmark, then follow a live Rocq proof session."""
import argparse
from contextlib import contextmanager
import datetime
import getpass
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True
from prover_models import ROOT, PROVIDERS, KEY_ENV, available_models, resolve_model

BENCHMARKS = ("preHorners", "Horners", "interchange_2x2", "monitor", "contour_row", "contour_right")


def positive(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return number


def nonnegative(value):
    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be zero or a positive integer")
    return number


def menu(title, choices):
    print(f"\n{title}")
    for index, (label, _) in enumerate(choices, 1):
        print(f"  {index:2}. {label}")
    while True:
        selected = input("Select a number: ").strip()
        if selected.isdigit() and 1 <= int(selected) <= len(choices):
            return choices[int(selected) - 1][1]
        print("Enter one of the listed numbers.")


def read_key(provider, file=None):
    if file:
        key = file.read_text().strip()
    else:
        key = os.environ.get(KEY_ENV[provider], "")
        if provider == "google" and not key:
            key = os.environ.get("GOOGLE_API_KEY", "")
        if not key and sys.stdin.isatty():
            key = getpass.getpass(f"{KEY_ENV[provider]} (hidden; not saved): ").strip()
    if not key:
        raise ValueError(f"Supply {KEY_ENV[provider]} or --key-file for the selected model")
    return key


def with_prerequisite(g, path):
    """Use a user's own checked preHorners proof without distributing a solution."""
    from types import FunctionType, SimpleNamespace
    normalized, reason = g.screen(path.read_text(), g.baseline_declaration("preHorners"), allowed_tactics=g.POLICY)
    if reason:
        raise ValueError("The supplied preHorners prerequisite failed statement/action screening: " + reason)
    def prerequisite():
        return "Require Import rec.\n" + normalized + "\nPrint Assumptions preHorners.\n"
    prepare = FunctionType(g.prepare.__code__, dict(g.prepare.__globals__, preHorners_prerequisite=prerequisite),
                           argdefs=g.prepare.__defaults__, closure=g.prepare.__closure__)
    return SimpleNamespace(**dict(g.__dict__, prepare=prepare, preHorners_prerequisite=prerequisite))


def read_state(interface):
    """Inspect every goal collection; an observation error is never completion."""
    if interface.finished:
        return dict(focused=[], background=[], shelved=[], given_up=[], focus_instruction=None)
    answer = interface._pf.current_goals
    if answer is None or answer.goals is None:
        raise RuntimeError("Rocq did not return the current proof state")
    config = answer.goals
    def rows(goals):
        return [dict(goal=g.ty, hypotheses=[dict(names=list(h.names), type=h.ty) for h in g.hyps]) for g in goals]
    return dict(focused=rows(config.goals),
                background=[dict(before=rows(left), after=rows(right)) for left, right in config.stack],
                shelved=rows(config.shelf), given_up=rows(config.given_up), focus_instruction=config.bullet)


def show_state(state):
    groups = [("Goal", state["focused"])]
    for index, frame in enumerate(state["background"], 1):
        groups += [(f"Background {index} before", frame["before"]), (f"Background {index} after", frame["after"])]
    groups += [("Shelved", state["shelved"]), ("Given up", state["given_up"])]
    count = 0
    for label, goals in groups:
        for index, goal in enumerate(goals, 1):
            count += 1
            print(f"\n  {label} {index}: {goal['goal']}")
            for hypothesis in goal["hypotheses"]:
                print(f"    {', '.join(hypothesis['names'])}: {hypothesis['type']}")
    if not count:
        print("  No remaining obligations; completion still requires Qed and independent validation.")
    elif not state["focused"]:
        print("  No focused goal; background or shelved obligations remain.")
    if state["focus_instruction"]:
        print(f"  Focus instruction: {state['focus_instruction']}")
    print(flush=True)


@contextmanager
def session_runtime(prover, g, calls, inputs, target, output, verbose):
    """Configure the checked proof-construction session."""
    from coq_interface import CoqInterface
    import proof_syntax as syntax
    from proof_closure import make_whole_proof_attempt
    from types import FunctionType

    names = ["BACKEND", "MODEL", "EFFORT", "RUN_DIR", "CHAT_LOG", "VERBOSE", "LAST_USAGE", "_api_call",
             "get_prompt", "get_pap_proof", "CoqInterface", "extract_tactics", "parse_plan",
             "try_tactics_in_coq", "prove_segment", "try_whole_proof", "_temperature_sent"]
    saved = {name: getattr(prover, name) for name in names}
    active = [None]

    def record(event):
        with (output / "progress.jsonl").open("a") as log:
            log.write(json.dumps(event, ensure_ascii=False) + "\n")

    class LiveInterface(CoqInterface):
        def __init__(self):
            self._pf = self._proof = self._tmpfile = None
            self._workspace = tempfile.TemporaryDirectory(prefix="coq-", dir=output)
            self._tmpdir = self._workspace.name
            self.finished = False

        def publish(self, event):
            state = read_state(self)
            record(dict(event=event, state=state))
            (output / "proof_state.json").write_text(json.dumps(state, indent=2, ensure_ascii=False) + "\n")
            if self._tmpfile and Path(self._tmpfile).is_file():
                (output / "live_prefix.v").write_text(Path(self._tmpfile).read_text())
            show_state(state)

        def open_proof(self, source):
            super().open_proof(source)
            active[0] = self
            self.publish("proof_opened")

        def goals(self):
            state = read_state(self)
            return [(goal["goal"], ", ".join(f"{', '.join(h['names'])} : {h['type']}" for h in goal["hypotheses"]))
                    for goal in state["focused"]]

        def try_tactic(self, tactic):
            tactic = tactic.strip()
            if not syntax.structural_action(tactic) and not tactic.endswith("."):
                tactic += "."
            reason = None
            if not syntax.structural_action(tactic):
                _, reason = g.screen(g.baseline_declaration(target) + "\nProof.\n" + tactic + "\nQed.",
                                    g.baseline_declaration(target), allowed_tactics=g.POLICY)
            if reason:
                accepted, error = False, "Action policy: " + reason
            else:
                try:
                    self._pf.append_step(self._proof, "\n  " + tactic)
                    accepted, error = True, ""
                except Exception as failure:
                    accepted, error = False, str(failure)
            print(f"  {'✓' if accepted else '✗'} {tactic}", flush=True)
            if error:
                print(f"    {error}", flush=True)
            record(dict(event="tactic", tactic=tactic, accepted=accepted, error=error))
            self.publish("tactic_accepted" if accepted else "tactic_rejected")
            return accepted, error

        def qed(self):
            accepted, error = super().qed()
            self.finished = accepted
            record(dict(event="qed", accepted=accepted, error=error))
            if accepted:
                self.publish("qed_accepted")
            return accepted, error

        def close(self):
            if active[0] is self:
                active[0] = None
            try:
                super().close()
            finally:
                self._workspace.cleanup()

    def invoke(system, messages, temperature, label):
        g.verify_inputs(target)
        if active[0] and label not in ("whole-proof", "session:init"):
            # Retain this augmentation in the session's visible history, so
            # later signed-native history matches the same logical prefix.
            messages[-1]["content"] += "\n\nComplete current Rocq state:\n" + json.dumps(read_state(active[0]), ensure_ascii=False)
        g.audit_request(system, messages, inputs)
        response = calls.invoke(system, messages, temperature, label)
        prover.LAST_USAGE = calls.last_usage
        return response

    prompt = saved["get_prompt"]
    def get_prompt(name):
        if name == "system_proof_assistant":
            return inputs["system"]
        if name == "library_summary":
            return inputs["library_summary"]
        result = prompt(name)
        if name in ("prompt_whole_proof", "prompt_plan"):
            result = result.replace("{theorem}", g.context(target) + "\n{theorem}")
        return result

    def parse_plan(raw):
        try:
            return syntax.parse_plan(raw, saved["parse_plan"])
        except Exception as error:
            print(f"  Plan rejected: {error}")
            return []

    prover.BACKEND = calls.config["provider"]
    prover.MODEL, prover.RUN_DIR, prover.CHAT_LOG = calls.config["id"], output, []
    prover.EFFORT = calls.config.get("effort")
    prover.VERBOSE = verbose
    prover._api_call, prover.CoqInterface = invoke, LiveInterface
    prover.get_prompt, prover.get_pap_proof = get_prompt, lambda name: inputs["paper"]
    prover.extract_tactics, prover.parse_plan = syntax.extract_tactics, parse_plan
    prover._temperature_sent = lambda value: value if calls.config["provider"] == "anthropic" and calls.config.get("thinking") == "off" else 1.0 if calls.config["provider"] == "google" else None
    prover.try_tactics_in_coq = lambda coq, tactics: syntax.replay(coq, tactics)
    prover.try_whole_proof = make_whole_proof_attempt(prover, record)
    try:
        yield
    finally:
        for name, value in saved.items():
            setattr(prover, name, value)


def parser():
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--list", action="store_true", help="list models and benchmarks; no model calls")
    result.add_argument("--model", help="registered or custom provider model ID")
    result.add_argument("--benchmark", choices=BENCHMARKS)
    result.add_argument("--provider", choices=PROVIDERS, help="required for unlisted model IDs")
    result.add_argument("--models-file", type=Path, help="alternative model registry")
    result.add_argument("--key-file", type=Path, help="read the selected provider's key from a local file")
    result.add_argument("--prerequisite", type=Path, help="for Horners, a complete preHorners declaration and proof from your own local run")
    result.add_argument("--effort", choices=("none", "low", "medium", "high"))
    result.add_argument("--thinking", choices=("off", "manual", "adaptive"))
    result.add_argument("--max-output", type=positive, help="output allowance per provider request")
    result.add_argument("--max-calls", type=nonnegative, default=0, help="optional request limit; 0 uses workflow termination")
    result.add_argument("--plan-rounds", type=positive, default=2)
    result.add_argument("--timeout", type=positive, default=600, help="provider request timeout in seconds")
    result.add_argument("--output", type=Path, help="new local directory for this session")
    result.add_argument("--prepare", action="store_true", help="compile dependencies and prepare prompts without any model request")
    result.add_argument("--verbose", action="store_true", help="also display model prompts and replies")
    return result


def main(argv=None):
    args = parser().parse_args(argv)
    models = available_models(args.models_file)
    if args.list:
        for model in models:
            print(f"{model['id']:30} {model['provider']}")
        print("\nBenchmarks: " + ", ".join(BENCHMARKS))
        return 0
    if not args.model or not args.benchmark:
        if not sys.stdin.isatty():
            raise ValueError("Supply --model and --benchmark, or run in a terminal for the selection menu")
        if not args.model:
            args.model = menu("Model", [(m["label"], m["id"]) for m in models] + [("Another model", "custom")])
            if args.model == "custom":
                args.provider = menu("Provider", [(p, p) for p in PROVIDERS])
                args.model = input("Provider model ID: ").strip()
                if not args.model:
                    raise ValueError("A model ID is required")
                if args.provider == "anthropic" and args.thinking is None:
                    args.thinking = menu("Thinking mode", [(mode, mode) for mode in ("off", "manual", "adaptive")])
        if not args.benchmark:
            args.benchmark = menu("Benchmark", [(name, name) for name in BENCHMARKS])
    config = resolve_model(args.model, args.provider, registry=args.models_file,
                           effort=args.effort, thinking=args.thinking, max_output=args.max_output)
    import guided_inputs
    import proof_syntax
    g = proof_syntax.validation_inputs(guided_inputs)
    g.verify_inputs(args.benchmark)
    if args.prerequisite:
        if args.benchmark != "Horners":
            raise ValueError("--prerequisite is only needed for Horners")
        g = with_prerequisite(g, args.prerequisite)
    # A missing prerequisite fails before prompting for credentials or making
    # any paid request. No target reference is loaded for the other five tasks.
    if args.benchmark == "Horners":
        try:
            g.preHorners_prerequisite()
        except (OSError, RuntimeError) as error:
            raise ValueError("Horners needs a checked preHorners prerequisite. Supply --prerequisite with candidate.v from your own successful preHorners run. No API request was made.") from error
    key = None if args.prepare else read_key(config["provider"], args.key_file)
    output = (args.output or ROOT / "runs" /
              (args.benchmark + "-" + datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%f"))).resolve()
    if output == ROOT or output.is_relative_to(ROOT / "benchmarks") or output.is_relative_to(ROOT / "prover"):
        raise ValueError("Choose a new session output directory outside source inputs")
    output.mkdir(parents=True, exist_ok=False, mode=0o700)
    result = dict(accepted=False, model=config["id"], provider=config["provider"], benchmark=args.benchmark,
                  mode="prepare" if args.prepare else "live", calls=0, verdict="preparing")
    (output / "session.json").write_text(json.dumps(dict(config=config, plan_rounds=args.plan_rounds,
        timeout=args.timeout, max_calls=args.max_calls, guidance="full",
        prerequisite_sha256=hashlib.sha256(args.prerequisite.read_bytes()).hexdigest() if args.prerequisite else None), indent=2) + "\n")
    calls = None
    try:
        print(f"\nModel: {config['id']} ({config['provider']})\nBenchmark: {args.benchmark}\nOutput: {output}", flush=True)
        print(f"Output allowance: {config['max_output']} tokens/request; plan rounds: {args.plan_rounds}", flush=True)
        g.prepare(args.benchmark, output)
        inputs = g.bundle(args.benchmark)
        if args.prepare:
            result["verdict"] = "prepared_without_model_calls"
            print("Dependencies checked and prompts prepared. No model calls made.")
            return 0
        sys.path.insert(0, str(ROOT / "prover"))
        import checkpoint_prover as prover
        from prover_api import ProviderCalls, ProviderStop
        calls = ProviderCalls(config, key, output, timeout=args.timeout, max_calls=args.max_calls)
        with session_runtime(prover, g, calls, inputs, args.benchmark, output, args.verbose):
            completed, actions = prover.prove_theorem(g.live_preamble(args.benchmark, output),
                g.baseline_declaration(args.benchmark), args.benchmark, n_attempts=args.plan_rounds)
        candidate = g.baseline_declaration(args.benchmark) + "\nProof.\n" + "\n".join(actions) + "\nQed.\n"
        if completed:
            (output / "candidate.v").write_text(candidate)
            result.update(g.validate(args.benchmark, candidate, output))
            result["verdict"] = "independently_verified" if result["accepted"] else result["reason"]
        else:
            (output / "partial.v").write_text(candidate.removesuffix("Qed.\n") + "Admitted.\n")
            result["verdict"] = "proof_search_exhausted"
        print(f"\nResult: {result['verdict']}\nSession files: {output}", flush=True)
        return 0 if result["accepted"] else 1
    except KeyboardInterrupt:
        result["verdict"] = "interrupted"
        print(f"\nStopped. Latest proof state and prefix remain in {output}")
        return 130
    except Exception as error:
        result.update(verdict="stopped", error_type=type(error).__name__)
        from prover_api import ProviderStop
        detail = str(error) if isinstance(error, (ProviderStop, RuntimeError)) else type(error).__name__
        print(f"\nStopped: {detail}\nSession files: {output}", file=sys.stderr)
        return 1
    finally:
        try:
            if calls:
                result["calls"] = calls.count
                calls.close()
        finally:
            (output / "result.json").write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    os.umask(0o077)
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        print(f"Stopped: {error}", file=sys.stderr)
        sys.exit(2)
