"""Replay a proposed proof, then try generic closers on the checked prefix."""
CLOSERS = ('auto.', 'reflexivity.', 'series_reflexivity.')


def make_whole_proof_attempt(prover, record):
    """Bind the existing API, parser and checked Coq interface at call time."""
    def attempt(preamble, theorem, name, pap, temperature=0.2):
        prompt = prover.get_prompt('prompt_whole_proof').format(
            library_summary=prover.get_prompt('library_summary'), theorem=theorem,
            pap_proof=pap, error_block='')
        raw = prover._chat(prover.get_prompt('system_proof_assistant'), prompt,
                           temperature, label='whole-proof')
        tactics = prover.extract_tactics(raw)
        if not tactics:
            record({'event':'whole_proof_outcome', 'success':False,
                    'reason':'no_parsed_tactics', 'pipeline_assisted':False})
            return False, []
        coq = prover.CoqInterface()
        try:
            coq.open_proof(preamble+'\n\n'+theorem+'\nProof.\nAdmitted.\n')
            applied, error = prover.try_tactics_in_coq(coq, tactics)
            prefix_length = len(applied)
            closers = []
            ok, _ = coq.qed()
            if not ok:
                for closer in CLOSERS:
                    accepted, _ = coq.try_tactic(closer)
                    if not accepted:
                        continue
                    applied.append(closer)
                    closers.append(closer)
                    ok, _ = coq.qed()
                    if ok:
                        break
            record({'event':'whole_proof_outcome', 'success':ok,
                    'replay_error':error, 'model_actions_applied':prefix_length,
                    'appended_closers':closers,
                    'pipeline_assisted':bool(ok and (error or closers)),
                    'raw_model_replay_succeeded':bool(ok and not error and not closers)})
            return ok, applied
        finally:
            coq.close()
    return attempt
