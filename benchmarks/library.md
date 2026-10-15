# Ruby relations in the Rocq library

This document describes the representation shared by the tasks. The accompanying
interface gives the exact definitions and signatures available for a particular
target. Only those listed modules and prerequisites belong to its fixed context.
Section variables and hypotheses in the interface describe parameters of the
exported definitions and lemmas. They do not add assumptions to the target.

## Relations and ports

`rel A B` means `A -> B -> Prop`: a relation between input values of type A and
output values of type B. It does not imply totality or single-valuedness. A Ruby
relation from A to B is written mathematically as a subset of A×B. Equality of
relations is extensional equality, using functional and propositional
extensionality as the two established foundational axioms.

Series `R;S` composes left to right: an intermediate value satisfies both
relations. Parallel `[R,S]` applies independent relations to the two components
of a product. `id A` is identity. `R^~1` denotes converse, not an automatically
existing inverse. Mathematical E^{-k} abbreviates `(E^~1)^^k`; inverse-style
cancellation requires the stated hypotheses. `R ^^ n` is the n-fold power,
with identity at zero. `FST R` and `SND R` apply R to one port and identity to
the other. The untouched port is implicit and must have the correct type.

`lsh` and `rsh` reassociate product ports. `fork` duplicates a value. Neither
product reassociation nor duplicate wiring adds an assumption about circuit
relations. `det R` means single-valuedness, without totality.

## Vector circuits

`t A n` is a length-indexed vector. `apr n` appends an element to an n-vector;
`apl n` prepends an element. These are relations induced by bijective wiring.
Their converses separate the element from the vector; the applicable identity
and port types are given in the interface. `mapn n R` applies R componentwise.
`tri n E` implements successive powers I,E,...,E^{n-1}. Its zero-size case is
the unique empty-vector identity.

`rdr n R` reduces a vector with a right-side accumulator; `rdl n R` reduces
with a left-side accumulator. Their exact port types differ. The beside and
below operators are `<-->` and `<||>` in Rocq, corresponding to the mathematical
↔ and ↕. `row`, `col` and `grid` build regular arrays with explicit vector wiring.
An empty row or column preserves its remaining scalar interface; it is not
an identity on an arbitrarily chosen product type.

## Index equality and transport

Mathematical equalities between lengths need not be definitional equalities in
Rocq. `cast_rel H`, for H:m=n, transports a vector from `t A m` to `t A n`.
It represents value-preserving reindexing. In monitor, an explicit cast remains
in P; the separately proved `P_as_PP` bridge relates P to a structurally indexed
form. The natural-number equality uniqueness used by the transport lemmas is
proved in the standard library, not an additional assumed axiom.

## General proof interface

Ordinary introductions, induction, proved local assertions and equality
reasoning are available subject to the recorded action policy. Function
arguments involving parallel expressions require parentheses, for example
`([R,S])`. Implicit type parameters can be made explicit with `@` or named
parameters when multiple port types fit the syntax.

Series association often hides a mathematical subexpression. `norm_left` and
`norm_right` normalise association. `series_rewrite` and `series_rewrite_rev`
apply an equality along series chains; the `_lhs` and `_rhs` variants choose a
side, and `_rev` variants reverse the equality. `series_reflexivity` closes
equalities differing only in series association. `rel_ext` provides pointwise
extensional reasoning when needed. These are generic library tools, not
target-specific solvers; their implementations are locally checked and withheld
from the generation interface.

The model must prove every local assertion and preserve the fixed target and
hypotheses. New imports, declarations, axioms, admissions, custom tactics and
unchecked proof terms are forbidden. Final acceptance requires statement/action
checks, compilation, expected assumptions and independent kernel replay.
