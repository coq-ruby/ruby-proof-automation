# Horner's transformation

Let P:A→A, Q:B→B and R:A×B→B be relations satisfying [P,Q];R=R;Q.
The triangle of length n applies I,P,...,P^{n-1} to its vector ports. The
right reduction combines these ports with a B accumulator using R. We prove
\[
[\operatorname{triangle}_n P,Q^n];\operatorname{rdr}_n R
 =\operatorname{rdr}_n(\operatorname{snd}Q;R).
\]
The permitted power-commutation law is
[P^k,Q^k];R=R;Q^k, derived from the stated cell equality.

Induct on n. At zero the vector is empty, the triangle is its identity, and
the reduction passes the B accumulator through. Both sides are that pass-through.

For the successor put T=triangle_n P, W=apr_n, and
S=snd Q;R. The append wire W joins an n-vector and its final element.
The recursive definitions are
triangle_{n+1}P=W^{-1};[T,P^n];W and
rdr_{n+1}R=fst(W^{-1});lsh;snd R;rdr_n R.
Thus, using wiring cancellation and parallel/series exchange,
\[
\begin{aligned}
[\operatorname{triangle}_{n+1}P,Q^{n+1}];\operatorname{rdr}_{n+1}R
 &= [W^{-1};[T,P^n];W,Q^n;Q];\operatorname{fst}(W^{-1});
       \operatorname{lsh};\operatorname{snd}R;\operatorname{rdr}_nR\\
 &= \operatorname{fst}(W^{-1});[[T,P^n],Q^n;Q];
       \operatorname{lsh};\operatorname{snd}R;\operatorname{rdr}_nR\\
 &= \operatorname{fst}(W^{-1});\operatorname{lsh};
       [T,[P^n,Q^n;Q]];\operatorname{snd}R;\operatorname{rdr}_nR\\
 &= \operatorname{fst}(W^{-1});\operatorname{lsh};
       [T,[P^n,Q;Q^n];R];\operatorname{rdr}_nR\\
 &= \operatorname{fst}(W^{-1});\operatorname{lsh};
       [T,\operatorname{snd}Q;[P^n,Q^n];R];\operatorname{rdr}_nR\\
 &= \operatorname{fst}(W^{-1});\operatorname{lsh};
       [T,\operatorname{snd}Q;R;Q^n];\operatorname{rdr}_nR\\
 &= \operatorname{fst}(W^{-1});\operatorname{lsh};\operatorname{snd}S;
       [T,Q^n];\operatorname{rdr}_nR\\
 &= \operatorname{fst}(W^{-1});\operatorname{lsh};\operatorname{snd}S;
       \operatorname{rdr}_nS\\
 &= \operatorname{rdr}_{n+1}S.
\end{aligned}
\]
The first simplification cancels W;W^{-1}; the next moves reassociation wiring
through the parallel block. Powers commute with the same relation, so
Q^n;Q=Q;Q^n. The power-commutation law acts on [P^n,Q^n];R in the second
branch. The penultimate equality is the induction hypothesis. The final
equality is the reduction recurrence. No extra property of P,Q or R is used.
