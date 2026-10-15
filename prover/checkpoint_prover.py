"""Construct proofs through whole-proof attempts and goal-driven checkpoints.

The session runner supplies the provider, benchmark inputs and live Rocq
interface. Planning and checkpoint turns share a conversation containing the
theorem, library interface and mathematical guidance.
"""
import json
from pathlib import Path
import re
import sys

from coq_interface import CoqInterface
from proof_closure import make_whole_proof_attempt
from proof_syntax import extract_tactics, replay as try_tactics_in_coq, structural_action

RUN_DIR: Path | None = None
CHAT_LOG: list[dict] = []
PROMPTS_DIR = Path(__file__).parent / 'prompts'
BACKEND = ''
MODEL = ''
EFFORT = None
VERBOSE = False
LAST_USAGE = None
_cache: dict[str, str] = {}


def _api_call(system, messages, temperature, label):
    raise RuntimeError('Configure a provider with scripts/run_prover.py')


def _temperature_sent(temperature):
    return temperature


def get_pap_proof(name):
    return (Path(__file__).resolve().parents[1] / 'benchmarks' / name / 'paper_proof.md').read_text()


try_whole_proof = make_whole_proof_attempt(sys.modules[__name__], lambda event: None)


def _chat(system: str, user: str, temperature: float = 0.2,
          label: str = "") -> str:
    """Single-shot LLM call (no conversation history)."""
    if label:
        print(f"  │      [{label}] ", end="", flush=True)
    result = _api_call(system, [{"role": "user", "content": user}],
                       temperature, label)
    if label:
        print(f"({len(result)}c)", flush=True)
    _log_exchange(label, temperature, system, user, result)
    return result


def _log_exchange(label, temperature, system, user, result):
    entry = {"label": label,
             "model": MODEL,
             "temperature": temperature,                  # requested
             "temperature_sent": _temperature_sent(temperature),  # transmitted
             "effort": EFFORT,
             "usage": LAST_USAGE,
             "system": system, "user": user, "assistant": result}
    CHAT_LOG.append(entry)
    if RUN_DIR:
        with open(RUN_DIR / "chat_history.jsonl", "a") as f:
            f.write(json.dumps(entry) + "\n")
    if VERBOSE and label:
        _print_verbose(label, user, result, temperature)


def _print_verbose(label, user, result, temperature):
    display = user
    lib_marker = "RELATIONAL ALGEBRA LIBRARY"
    for end_m in ["THEOREM:", "CURRENT COQ", "PEN-AND-PAPER", "We will prove"]:
        start = display.find(lib_marker)
        if start >= 0:
            end_pos = display.find(end_m, start + 100)
            if end_pos >= 0:
                display = display[:start] + f"[library: {end_pos-start}c]\n" + display[end_pos:]
                break
    sent = _temperature_sent(temperature)
    tstr = f"t={temperature}" if sent is not None else f"t={temperature}→not sent"
    print(f"  │      ┄┄ PROMPT ({len(user)}c, {tstr}) ┄┄")
    for line in display.strip().split("\n"):
        print(f"  │      ┊ {line}")
    print(f"  │      ┄┄ RESPONSE ┄┄")
    for line in result.split("\n"):
        print(f"  │      ┊ {line}")
    print(f"  │      ┄┄ END ┄┄")


class Session:
    """Multi-turn conversation. Context (library, theorem, pap) is sent
    once in the opening message. Subsequent calls are focused."""

    def __init__(self, system: str, opening_message: str, temperature: float = 0.2):
        self.system = system
        self.temperature = temperature
        self.messages: list[dict] = []   # alternating user/assistant
        self.turn_count = 0

        # Send opening message
        reply = self._send(opening_message, "session:init")
        self.turn_count += 1

    def ask(self, user_msg: str, label: str = "",
            temperature: float | None = None) -> str:
        """Send a follow-up message in the conversation."""
        temp = temperature if temperature is not None else self.temperature
        self.temperature = temp  # update for this call
        reply = self._send(user_msg, label)
        self.turn_count += 1
        return reply

    def inject_result(self, text: str):
        """Add a synthetic assistant message (e.g. Coq verification result)
        so the model sees it as part of the conversation history."""
        self.messages.append({"role": "assistant", "content": text})

    def _send(self, user_msg: str, label: str) -> str:
        self.messages.append({"role": "user", "content": user_msg})
        print(f"  │      [{label}] ", end="", flush=True)
        result = _api_call(self.system, self.messages,
                           self.temperature, label)
        print(f"({len(result)}c)", flush=True)
        self.messages.append({"role": "assistant", "content": result})
        _log_exchange(label, self.temperature, self.system,
                      user_msg, result)
        return result


def get_prompt(name: str) -> str:
    if name not in _cache:
        p = PROMPTS_DIR / f"{name}.txt"
        if not p.exists(): sys.exit(f"Missing prompt: {p}")
        _cache[name] = p.read_text()
    return _cache[name]


def _normalize_tactic(t: str) -> str:
    t = t.strip()
    t = re.sub(r'^(series_rewrite(?:_lhs|_rhs)?)\s+<-\s+',
               lambda m: m.group(1) + '_rev ', t)
    return t


def fmt_goals(goals: list) -> str:
    if not goals: return "(no goals — proof may be complete)"
    parts = []
    if len(goals) > 1:
        parts.append(f"[{len(goals)} subgoals — focus on the first]")
    for i, (ty, hyps) in enumerate(goals):
        if i == 0:
            parts.append(f"Goal: {ty}")
            if hyps: parts.append(f"Hyps: {hyps}")
        else: parts.append(f"Subgoal {i+1}: {ty}")
    return "\n".join(parts)


def advance_goals(coq, applied: list[str]) -> list:
    """Get current goals. If empty (possibly needs a bullet), try bullets.
    Returns the goal list and appends any bullet to applied."""
    gs = coq.goals()
    if gs:
        return gs
    # goals() returned empty — might need a bullet to enter next subgoal
    for bullet in ["-", "+", "*", "--", "++"]:
        ok, _ = coq.try_tactic(bullet)
        if ok:
            applied.append(bullet)
            print(f"  │        (auto-bullet: {bullet})")
            gs = coq.goals()
            if gs:
                return gs
    return []


def parse_plan(raw: str) -> list[dict]:
    segments = []
    for block in re.split(r"SEGMENT\s+", raw):
        block = block.strip()
        if not block: continue
        label_m = re.match(r"(\w+)\s*:", block)
        label = label_m.group(1) if label_m else f"seg_{len(segments)}"
        pap_m = re.search(r"pap:\s*(.+?)(?=\n\s*after:|\Z)", block, re.DOTALL)
        after_m = re.search(r"after:\s*(.+?)(?=\nSEGMENT|\Z)", block, re.DOTALL)
        segments.append({
            "label": label,
            "pap_excerpt": pap_m.group(1).strip() if pap_m else "",
            "target": after_m.group(1).strip() if after_m else "",
        })
    return segments


def prove_segment(session: Session, coq, segment: dict,
                  theorem: str) -> tuple[bool, list[str]]:
    """Prove one segment using the conversation session.
    Tries batch first, then incremental — all within the same session."""
    label = segment.get("label", "?")
    all_applied: list[str] = []

    # ── Batch attempts ───────────────────────────────────────
    for retry in range(3):
        gs = coq.goals()
        if not gs: return True, all_applied

        goal_str = fmt_goals(gs)

        if retry == 0:
            msg = (f"SEGMENT [{label}]\n"
                   f"Current Coq goal:\n{goal_str}\n\n"
                   f"Algebraic step:\n{segment.get('pap_excerpt','')}\n\n"
                   f"Expected result:\n{segment.get('target','')}\n\n"
                   f"Write the Coq tactics for this segment in a ```coq block.")
        else:
            msg = (f"That failed. Current goal is now:\n{goal_str}\n\n"
                   f"Try a different approach for segment [{label}].\n"
                   f"Write tactics in a ```coq block.")

        temp = 0.2 + retry * 0.15
        raw = session.ask(msg, label=f"seg:{label}", temperature=temp)
        tactics = extract_tactics(raw)
        if not tactics: continue

        applied, err = try_tactics_in_coq(coq, tactics)
        all_applied.extend(applied)

        for a in applied:
            print(f"  │        ✓ {a}")

        if err is None:
            # All tactics succeeded — tell the session
            gs_after = coq.goals()
            session.inject_result(
                f"All {len(applied)} tactics succeeded. "
                f"{'No goals remaining.' if not gs_after else f'Current goal: {gs_after[0][0][:80]}...'}"
            )
            return True, all_applied

        print(f"  │        ✗ {err[:70]}")
        # Inject failure as assistant context
        session.inject_result(
            f"{len(applied)} tactics worked, then: {err}"
        )

    # ── Incremental fallback ─────────────────────────────────
    print(f"  │      batch stuck, switching to incremental")
    for step in range(8):
        gs = coq.goals()
        if not gs: return True, all_applied

        goal_str = fmt_goals(gs)
        msg = (f"Incremental mode for [{label}]. Goal:\n{goal_str}\n\n"
               f"Write exactly 1 tactic in a ```coq block.")

        temp = 0.2 + step * 0.05
        raw = session.ask(msg, label=f"incr:{label}", temperature=temp)
        tactics = extract_tactics(raw)

        made_progress = False
        for t in tactics[:2]:  # at most 2 tactics
            t = _normalize_tactic(t)
            if not structural_action(t) and not t.endswith("."): t += "."
            ok, err = coq.try_tactic(t)
            if ok:
                all_applied.append(t)
                made_progress = True
                print(f"  │        ✓ {t}")
                session.inject_result(f"✓ {t}")
            else:
                print(f"  │        ✗ {t}: {err[:50]}")
                session.inject_result(f"✗ `{t}` failed: {err[:80]}")
                break

        if not made_progress:
            # Try one alternative before ending this segment.
            gs2 = coq.goals()
            msg2 = (f"That tactic failed. Current goal:\n{fmt_goals(gs2)}\n"
                    f"Try something different.")
            raw2 = session.ask(msg2, label=f"incr:{label}", temperature=0.5)
            tactics2 = extract_tactics(raw2)
            for t in tactics2[:2]:
                t = _normalize_tactic(t)
                if not structural_action(t) and not t.endswith("."): t += "."
                ok, err = coq.try_tactic(t)
                if ok:
                    all_applied.append(t)
                    made_progress = True
                    print(f"  │        ✓ {t}")
                    session.inject_result(f"✓ {t}")
                    break
                else:
                    print(f"  │        ✗ {t}: {err[:50]}")
                    session.inject_result(f"✗ `{t}` failed: {err[:80]}")

            if not made_progress:
                return False, all_applied

    return True, all_applied


def prove_theorem(preamble, theorem, name, n_attempts=3):
    pap = get_pap_proof(name)

    print(f"\n{'═'*60}")
    print(f"  Theorem: {name}")
    print(f"{'═'*60}")
    print(f"  {theorem[:200]}")

    # ── Phase 0: Quick whole proof ──────────────────────────
    print(f"\n  ┌─ Phase 0: whole proof")
    for att in range(2):
        ok, tactics = try_whole_proof(preamble, theorem, name, pap, 0.2 + att*0.2)
        if ok:
            print(f"  └─ ✅ Proved (whole proof, attempt {att+1})")
            return True, tactics
        print(f"  │  attempt {att+1}: {len(tactics)} tactics applied")
    print(f"  │  whole proof failed, moving to segments")

    # ── Phase 1+2+3: Segment-driven proving ─────────────────
    best_applied: list[str] = []

    for plan_round in range(n_attempts):
        print(f"\n  ┌─ Plan round {plan_round+1}/{n_attempts}")

        # Phase 1: Open session with full context, generate plan
        system = get_prompt("system_proof_assistant")
        plan_prompt = get_prompt("prompt_plan").format(
            library_summary=get_prompt("library_summary"),
            theorem=theorem, pap_proof=pap,
        )

        session = Session(system, plan_prompt, temperature=0.2)
        plan_raw = session.messages[-1]["content"]  # assistant's plan response
        segments = parse_plan(plan_raw)

        if not segments:
            print(f"  │  ✗ no segments generated")
            continue

        print(f"  │  {len(segments)} segments:")
        for s in segments:
            print(f"  │    [{s['label']}] {s.get('pap_excerpt','')[:60]}...")

        # Tell the session we're starting segment proving
        session.inject_result(
            "Plan accepted. I will now send you the actual Coq goal state "
            "for each segment. Reply with ONLY Coq tactics in a ```coq block."
        )

        # Phase 2: Prove each segment
        coq_source = f"{preamble}\n\n{theorem}\nProof.\nAdmitted.\n"
        coq = CoqInterface()
        try:
            coq.open_proof(coq_source)
            all_applied: list[str] = []
            stuck = False

            for seg_idx, segment in enumerate(segments):
                lbl = segment.get("label", f"seg_{seg_idx}")
                gs = advance_goals(coq, all_applied)
                if not gs: break

                print(f"  │  Segment {seg_idx+1}/{len(segments)} [{lbl}]")
                print(f"  │    goal: {gs[0][0][:70]}...")

                ok, seg_tactics = prove_segment(session, coq, segment, theorem)
                all_applied.extend(seg_tactics)

                if ok:
                    print(f"  │    ✓ done ({len(seg_tactics)} tactics)")
                else:
                    print(f"  │    ✗ stuck ({len(seg_tactics)} tactics)")
                    stuck = True
                    break

            # Phase 3: Assembly — try Qed
            if not stuck:
                gs = advance_goals(coq, all_applied)
                if not gs:
                    qok, _ = coq.qed()
                    if qok:
                        print(f"  └─ ✅ Proved by checkpoints "
                              f"(round {plan_round+1}, {len(all_applied)} tactics)")
                        return True, all_applied
                    # Qed failed even with no goals — try closers
                    print(f"  │  Qed failed (no visible goals)")
                else:
                    # Still have goals — try closers
                    for closer in ["auto.", "reflexivity.", "series_reflexivity."]:
                        cok, _ = coq.try_tactic(closer)
                        if cok:
                            all_applied.append(closer)
                            qok, _ = coq.qed()
                            if qok:
                                print(f"  └─ ✅ Proved by checkpoints + {closer}")
                                return True, all_applied
                    gs = coq.goals()
                    print(f"  │  Qed failed: {fmt_goals(gs)[:80]}")

            if len(all_applied) > len(best_applied):
                best_applied = list(all_applied)
                print(f"  │  (new best: {len(best_applied)} tactics)")

        finally:
            coq.close()

    print(f"\n  ❌ {name}: all strategies exhausted "
          f"(best: {len(best_applied)} tactics)")
    return False, best_applied
