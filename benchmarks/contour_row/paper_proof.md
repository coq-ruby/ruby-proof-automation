# Row contour transformation

Use series composition ;, parallel composition [P,Q], beside composition ↔,
fst/snd, row_n, triangle_n, and relational converse E^-1. Let E^-k=(E^-1)^k.
Powers at zero are identities. Let R:A×B→B×A be a relation, and
let EA and EB be endorelations on
A and B. Assume EA;EA^-1=I, EA^-1;EA=I, and
R=[EA,EB];R;[EB^-1,EA^-1]. No cancellation property of EB is required.

Write T_k=triangle_k EB, Tbar_k=triangle_k(EB^-1), and R_E=R;snd EA.
The paired conjugation expands to R=[EA,EB];R;[EB^-1,EA^-1].
Repeated substitution, associativity and parallel powers give
R=[EA^k,EB^k];R;[EB^-k,EA^-k] for every natural k.
The two EA cancellation laws give EA^-k;EA^k=I and
EA^-k=EA;EA^-(k+1), respectively. These are equalities of relations, not
assumptions about existence or uniqueness of elementwise witnesses.

We prove, for every natural row length n,

```text
row_n R=snd(triangle_n EB);row_n(R;snd EA);
        [(triangle_n EB)^-1,EA^-n].
```

Proceed by induction on row length. At zero, the row connects the horizontal
input and output through the identity, all vectors are empty, and both the
triangle and zero powers are identities. The transformed zero row is the same
empty circuit.

For the successor n=k+1, the following is one continuous calculation. apr_k is
the standard Ruby append wire from (length-k vector,last element) to a length-
(k+1) vector. All factors retain their typed vector or horizontal interfaces.

```text
row_(k+1) R
 = snd(apr_k^-1);(row_k R ↔ R);fst apr_k
 = snd(apr_k^-1);
   ((snd T_k;row_k R_E;[Tbar_k,EA^-k])
    ↔ ([EA^k,EB^k];R;[EB^-k,EA^-k]));fst apr_k
 = snd(apr_k^-1);[I,[T_k,EB^k]];
   (row_k R_E ↔ (fst(EA^-k;EA^k);R));
   [[Tbar_k,EB^-k],EA^-k];fst apr_k
 = snd(apr_k^-1);[I,[T_k,EB^k]];
   (row_k R_E ↔ R);
   [[Tbar_k,EB^-k],EA;EA^-(k+1)];fst apr_k
 = snd T_(k+1);snd(apr_k^-1);
   (row_k R_E ↔ (R;snd EA));fst apr_k;
   [Tbar_(k+1),EA^-(k+1)]
 = snd T_(k+1);row_(k+1) R_E;[Tbar_(k+1),EA^-(k+1)]
 = snd(triangle_(k+1) EB);row_(k+1)(R;snd EA);
   [(triangle_(k+1) EB)^-1,EA^-(k+1)].
```

The second equality uses the prefix induction hypothesis and powered
conjugation of the final cell. The third is generic beside boundary exchange:
```text
(snd U;P;[V,H]) ↔ ([K,L];Q;[M,N])
 = snd[U,L];(P ↔ (fst(H;K);Q));[[V,M],N].
```

It composes H and K on the internal seam and moves the remaining independent
vertical factors to the external parallel boundaries. This law has no
cancellation or conjugation premise.

The fourth equality cancels the horizontal seam and extends the final inverse
power. In the fifth, move the remaining EA onto the last cell's right port and
collect the input and output factors through the append wires. The triangle's
defining recurrence is
triangle_(k+1) E=apr_k^-1;[triangle_k E,E^k];apr_k.
For any invertible interface wire W and compatible P,Q, boundary collection
uses the generic identities
snd(W^-1);snd P=snd(W^-1;P;W);snd(W^-1),
[P,Q];fst W=fst W;[W^-1;P;W,Q],
with W;W^-1=I. Here W=apr_k. The input and output vector boundaries are
T_(k+1) and Tbar_(k+1); no EB factors are cancelled.
Finally fold the append form of row and use
triangle_n(EB^-1)=(triangle_n EB)^-1 to obtain the exact target.

