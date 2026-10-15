# Representation of the relational monitor

The target is `forall n, P n = Q n`, under four premises: `D^~1;D=id A`,
`[D,D];R=R;D`, `rsh;FST R;R=SND R;R` and `det R`. D is an arbitrary
endorelation and R:rel (A*A) A. Neither totality nor the opposite D cancellation
law may be added.

In the mathematical guidance F_k is `mfork k`, Δ is `fork`, T_m is `PP m`,
triangle is `tri`, and left reduction is `rdl`. The explicit cast in P transports
a vector indexed by `2^n` to one indexed by `S (2^n-1)`, using `S2nM1 n`.
These lengths are mathematically equal but need not be definitionally equal in
Rocq. `cast_rel` uses equality transport without changing vector contents.

`P_as_PP : forall n, P n = PP (2^n-1)` is a checked representation bridge.
It does not redefine P or remove its cast without justification. Generic
`cast_tri` and `cast_mfork` express compatibility of triangle and replication
with reindexing. The bridge's proof is withheld from the model interface.
Arithmetic facts `Sn2`, `S2nM1` and `pow2_pos` describe doubling and positive
lengths. Natural-number equality uniqueness is a proved standard-library fact,
not an extra axiom.

The available modules are axioms, rel, basic, wire, rec and monitor_prerequisites
under `library/core/`. Generic signatures include `mfork_snoc`, `tri_S`,
`rdl_snoc`, `W2`, `fork_assoc`, `rsh_para`, `Hpush_pow`, `det_PP` and
`det_absorb`. The last three express power commutation, single-valuedness of
structural circuits and duplication of a single-valued relation. They are prior
facts used in the mathematical guidance. `PP0` supplies the singleton base circuit.

The structural successor identity, forked-tree reassociation and general block
split remain obligations inside the target proof. These results and all benchmark
solutions are absent from imports. The representation bridge and generic
determinism laws do not establish P=Q. Generic normalisation tools do not solve
monitor.

This benchmark formulates the monitor circuit relationally. Its four premises
are authoritative. Adapting the functional argument to these premises and
handling the casts required human preparation. The only
foundational assumptions are functional and propositional extensionality.
