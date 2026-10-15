# Representation of Horner's transformation

Mathematical triangle_n P is `tri n P`; right reduction is `rdr n R`;
fst/snd and converse are FST/SND and `^~1`. The accumulator has type B and
the vector has type `t A n`. The target is a relation from `t A n * B` to B,
including the empty-vector case. Mathematical R:A×B→B is a relation.

The available modules are axioms, rel, basic, wire, loop and rec under
`library/core/`. The cell commutation law is a premise. A checked preHorners
proof is required: supply `candidate.v` from a successful local preHorners run
using `--prerequisite`. Its statement appears in `library_interface.v`; its
proof is checked locally and withheld from the model. No Horners solution is
supplied as input.

Generic laws include `para_series`, `para_lsh`, `apr_apr1`, `pow_left`,
`pow_right` and `mapn_rdr_id_zero`. These express exchange, reshaping, wire
cancellation, power recurrences and empty reduction. None concludes the
triangle/reduction transformation. Generic normalisation tools manipulate
series association. Mathematical guidance supplies the induction and algebraic
calculation; representation matching is explained in the shared library notes.

The only foundational assumptions are functional and propositional
extensionality. Cell commutation remains a theorem-specific premise.
