# Lifting a cell commutation law to powers

Let P:A→A, Q:B→B and R:A×B→B be relations, with
\[
[P,Q];R=R;Q.
\]
Composition is left to right, and powers include P⁰=I_A and Q⁰=I_B.
For every natural number n we prove
\[
[P^n,Q^n];R=R;Q^n.
\]

Induct on n. At zero, both sides are R by the parallel and series identity
laws. Suppose the result holds at n. Parallel/series exchange, the cell law
and the induction hypothesis give the continuous calculation
\[
\begin{aligned}
[P^{n+1},Q^{n+1}];R
 &= [P^n;P,Q^n;Q];R\\
 &= [P^n,Q^n];[P,Q];R\\
 &= [P^n,Q^n];R;Q\\
 &= R;Q^n;Q\\
 &= R;Q^{n+1}.
\end{aligned}
\]
No totality, determinism, cancellation or temporal interpretation is required.
