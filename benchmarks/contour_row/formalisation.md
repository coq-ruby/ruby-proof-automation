# Representation of the row contour

The statement is in `target.v`. EA:rel A A and EB:rel B B need not represent
delays. Both EA cancellation directions are explicit premises; no cancellation
of EB is assumed or required. The paired conjugation `R = R \ [EB^~1,EA^~1]`
expands to the cell equality in the mathematical guidance. `conj4_pair` and
converse involution express that notation correspondence.

Mathematical row_n, triangle_n, fst/snd and append wire are `row n`, `tri n`,
FST/SND and `apr n`. The target maps `A * t B n` to `t B n * A`.
Converse powers are `(EA^~1) ^^ n`. The zero case preserves the scalar A port
and uses empty B vectors. The mathematical argument concerns relation equalities
and assumes no additional functionality or elementwise witnesses.

The available modules are axioms, rel, basic, wire, wire_rec, rec, twod,
contour_prerequisites and equational_helpers. Their paths are listed in
`benchmarks/manifest.json`. Generic laws include `conjugation_power`,
`power_cancellation`, `inverse_power_extend`, `row_append`,
`beside_boundary_exchange`, `beside_final_factor`, `interface_input`,
`interface_output` and `triangle_converse`. Exact signatures appear in
`library_interface.v`. These express cell powers and structural wiring/exchange;
they do not establish the hypothesis-dependent row transformation. The uniform
power conjugation fact concerns a single relation, rather than an array contour.
No row-contour solution, equivalent pointwise result, repeated-cell shift/unshift
result or completed benchmark is imported. Generic association tactics do not
contain a contour solver.

The supplied derivation uses continuous append calculation. Append-boundary
collection and generic helper proofs required human proof engineering and form
part of the supplied context. The only foundational assumptions are functional
and propositional extensionality.
