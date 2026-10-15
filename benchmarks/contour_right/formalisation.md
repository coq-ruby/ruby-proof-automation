# Representation of the right-grid contour

This benchmark uses a reconstructed right-grid contour statement. A typed-D
mathematical derivation is generalised to EA:rel A A and EB:rel B B, with both
cancellation directions for each relation explicit. The paired conjugation
premise and all natural dimensions are preserved. The mathematical guidance
includes m=0 as well as positive-width cases. No temporal interpretation is assumed.

Mathematical grid_(m,n) is `grid m n`, a row of m columns each of height n.
Its type is `rel (t A n * t B m) (t B m * t A n)`. Triangle_m EB is `tri m EB`,
and map_n EA is `mapn n EA`. The prepend wire is `apl m`. Inverse notation is
relational converse. The cell-conjugation expansion follows from `conj4_pair`
and converse involution.

The available modules are axioms, rel, basic, wire, wire_rec, rec, twod,
contour_prerequisites, grid_helpers, equational_helpers and grid_support.
Their paths are listed in `benchmarks/manifest.json`. The supplied
`grid_conjugation` theorem is a separate outer-grid boundary law. It applies
uniform boundary factors without inserting EA into cells or forming triangular
boundaries. It is a proved prerequisite of this task, rather than an extra axiom.

Other supporting signatures include `grid_step`, `col_snd_mapn`, `beside_fst`,
`beside_snd`, `beside_block_para`, `triangle_prepend`, `triangle_prepend_right`,
`triangle_converse` and generic interface-wire laws. Uniform conjugation helpers
and prepend-triangle proofs required human proof engineering. These helpers do
not establish the per-cell right-contour transformation. No contour_row solution,
contour_right solution or general row/column interchange theorem is imported.
Generic normalisation tactics do not contain a grid-contour solver.

The mathematical guidance uses continuous grid induction with typed boundary
compositions and the reconstruction adjustments above. The only foundational
assumptions are functional and propositional extensionality.
