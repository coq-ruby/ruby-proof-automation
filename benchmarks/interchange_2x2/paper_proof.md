# Interchange of a two-by-two Ruby array

Let R be any relation from A×B to B×A. Beside composition joins horizontal
ports, and below composition joins vertical ports. We show
\[
(R\leftrightarrow R)\updownarrow(R\leftrightarrow R)
 =(R\updownarrow R)\leftrightarrow(R\updownarrow R).
\]
No commutation, cancellation or determinism premise is required.

Fix input ((a₁,a₂),(b₁,b₂)) and output ((c₁,c₂),(d₁,d₂)), where the a,d
values lie in A and the b,c values lie in B. Name the internal horizontal
wires h₁,h₂∈A and vertical wires v₁,v₂∈B. The four cells impose
\[
\begin{array}{ll}
C_{11}:R(a_1,v_1)(c_1,h_1), & C_{12}:R(h_1,v_2)(c_2,d_1),\\
C_{21}:R(a_2,b_1)(v_1,h_2), & C_{22}:R(h_2,b_2)(v_2,d_2).
\end{array}
\]
The beside/below definitions express membership in the row-first circuit as
\[
\exists v_1,v_2\;[(\exists h_1\;C_{11}\land C_{12})
                  \land(\exists h_2\;C_{21}\land C_{22})].
\]
The column-first circuit expresses it as
\[
\exists h_1,h_2\;[(\exists v_1\;C_{11}\land C_{21})
                  \land(\exists v_2\;C_{12}\land C_{22})].
\]
Both mean that the same four wires satisfy all four cell constraints. In each
direction retain their values and regroup the constraints by columns or rows.
The membership predicates are therefore equivalent for every input and output,
which establishes equality of the relations.
