# Representation of power commutation

The mathematical P, Q and R correspond to the parameters of `preHorners` in
`target.v`. An arrow denotes a relation `rel A B`, without totality or
single-valuedness. Powers are `pow n R` or `R ^^ n`, including identity at zero.
The cell commutation equality is a quantified premise of the target.

The available modules are axioms, rel, basic, wire, loop and rec under
`library/core/`. The shared library notes explain parallel/series exchange and
power notation; `library_interface.v` gives exact signatures. Generic power
identities and association tactics do not establish the hypothesis-dependent
commutation theorem. Neither preHorners nor Horners is imported as a prerequisite.

The mathematical guidance supplies induction on the natural dimension. The only
foundational assumptions are functional and propositional extensionality.
