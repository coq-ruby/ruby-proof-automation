"""
Thin CoqPyt wrapper. Opens a proof, reads goals, tries tactics.

Goal path: step.goals.goals.goals[0].ty / .hyps
Each tactic must be a separate append_step call.
Bullets (-/+/*) must be their own step.

Tested: Coq 8.19.2, coq-lsp 0.2.3, CoqPyt 0.0.1

Note on goals():
  In CoqPyt, step.goals contains the goals BEFORE that step executes
  (coq-lsp "sentence position" convention). To read the goals AFTER
  the last tactic, we append a no-op probe (idtac.), read ITS pre-goals
  (= real post-goals of the last tactic), then pop the probe.

Note: the proof source passed to open_proof() must be fully self-contained
(all local Require imports and exports inlined). The benchmark loader builds
this source from the selected library modules and benchmark context.
"""

import os
import tempfile
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.exceptions import InvalidChangeException


class CoqInterface:
    def __init__(self):
        self._pf      = None
        self._proof   = None
        self._tmpdir  = tempfile.mkdtemp()
        self._tmpfile = None

    def open_proof(self, coq_source: str):
        """Write source to a temp .v file, open it with CoqPyt, remove Admitted."""
        fpath = os.path.join(self._tmpdir, "proof.v")
        self._tmpfile = fpath
        with open(fpath, "w") as f:
            f.write(coq_source)
        self._pf = ProofFile(fpath)
        self._pf.run()
        self._proof = self._pf.unproven_proofs[0]
        self._pf.pop_step(self._proof)  # remove Admitted.

    def _read_goals_from_step(self, step):
        """Extract (goal_ty, hyps_str) list from a proof step."""
        try:
            goal_list = step.goals.goals.goals
        except AttributeError:
            return []
        if not goal_list:
            return []
        results = []
        for g in goal_list:
            hyps = ", ".join(
                f"{', '.join(h.names)} : {h.ty}" for h in g.hyps
            )
            results.append((g.ty, hyps))
        return results

    def goals(self):
        """Return list of (goal_ty, hyps_str) for the CURRENT proof state.

        CoqPyt's step.goals gives the goals BEFORE that step executes.
        To get the true current state (after the last tactic), we append
        a no-op `idtac.` probe, read its pre-goals, then pop it.
        """
        if not self._proof or not self._proof.steps:
            return []
        try:
            self._pf.append_step(self._proof, "\n  idtac.")
        except Exception:
            # idtac failed to append — proof is likely complete (no goals)
            # IMPORTANT: do NOT pop_step here — nothing was added,
            # so popping would remove the last real tactic.
            return []
        # idtac was appended successfully — read its pre-goals then remove it
        try:
            probe = self._proof.steps[-1]
            result = self._read_goals_from_step(probe)
        finally:
            self._pf.pop_step(self._proof)
        return result

    def try_tactic(self, tactic: str):
        """Append a tactic. Returns (success, error_string)."""
        tactic = tactic.strip()
        if not tactic:
            return False, "empty tactic"
        if tactic not in ("-", "+", "*", "{", "}") and not tactic.endswith("."):
            tactic += "."
        try:
            self._pf.append_step(self._proof, f"\n  {tactic}")
            return True, ""
        except (InvalidChangeException, Exception) as e:
            return False, str(e)

    def qed(self):
        """Try closing with Qed. Returns (success, error_string)."""
        try:
            self._pf.append_step(self._proof, "\nQed.")
            return True, ""
        except (InvalidChangeException, Exception) as e:
            return False, str(e)

    def close(self):
        if self._pf:
            try:
                self._pf.__exit__(None, None, None)
            except Exception:
                pass