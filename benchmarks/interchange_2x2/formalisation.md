# Representation of two-by-two interchange

The mathematical ↔ and ↕ correspond to `<-->` and `<||>`. Product parentheses
represent port grouping and must be preserved. R has type `rel (A*B) (B*A)`;
`target.v` states the equality between row-first and column-first composition.

The available modules are axioms, rel, basic, wire and grid_components under
`library/core/`. The latter supplies beside/below definitions and the generic
pointwise characterisations `beside_dual` and `below_dual`. Their signatures
specify the existential seams; proof bodies are withheld from the model
interface. Extensional equality is explained in the shared library notes.
No general interchange theorem, two-by-two solution, or row/column/grid theorem
is imported. The witness correspondence remains the target obligation.

The complete witness argument is supplied as mathematical guidance. The only
foundational assumptions are functional and propositional extensionality.
There are no theorem-specific hypotheses or tactics that implement this result.
