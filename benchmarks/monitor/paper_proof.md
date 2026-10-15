# Relational avionics monitor transformation

Let D:A→A and R:A×A→A be relations, with
D^-1;D=I, [D,D];R=R;D, rsh;fst R;R=snd R;R,
and R single-valued. No totality or opposite cancellation law is assumed.
Composition is left to right; Δ duplicates an input; powers start at identity.

Let F_k replicate an input into a k-vector. Define the original circuit

P_n=F_(2^n);triangle_(2^n) D;κ_n;apl_(2^n-1)^-1;rdl_(2^n-1) R,

where κ_n is value-preserving reindexing from length 2^n to
length 1+(2^n-1). This equality of lengths holds because 2^n is positive.
Let Q_0=I and Q_(n+1)=Q_n;Δ;snd(D^(2^n));R. The target is P_n=Q_n.
For structural size m define

T_m=F_(m+1);triangle_(m+1) D;apl_m^-1;rdl_m R.

1. Remove only the vector-length bookkeeping.
The positive natural number 2^n equals 1+(2^n-1). Transport through the triangle and replicated vector respects this equality, so value-preserving reindexing gives P_n=T_(2^n-1). From the singleton triangle and singleton reduction, T_0=I. All later identities are about these cast-free T_m; the original P remains unchanged.

2. Derive the structural successor identity.
Replication of m+2 inputs can be expressed as Δ;[F_(m+1),I];apr_(m+1). The triangle of size m+2 is
apr_(m+1)^-1 ; [triangle_(m+1) D,D^(m+1)] ; apr_(m+1).
The reduction of m+2 inputs is
snd(apr_m^-1);rsh;fst(rdl_m R);R.
Insert these three expansions into the definition of T_(m+1). The adjacent apr_(m+1);apr_(m+1)^-1 cancels. The remaining vector wires obey
apr_(m+1);apl_(m+1)^-1;snd(apr_m^-1)
 = fst(apl_m^-1);lsh.
Cancel lsh;rsh. Collect the first-component operations using [U,V];[W,Z]=[U;W,V;Z]. The first component is exactly F_(m+1);triangle_(m+1)D;apl_m^-1;rdl_m R=T_m; the second is D^(m+1). Thus
T_(m+1)=Δ;[T_m,D^(m+1)];R.                         (S)
This is the first structural identity in the argument.

3. Establish the associativity identity for forked trees.
For arbitrary X,Y,Z : A→A relations, show
Δ;[Δ;[X,Y];R,Z];R = Δ;[X,Δ;[Y,Z];R];R.            (T)
On the left, separate the two parallel branches, collect the operations on the first component, and move the independent Z branch past the first application of R. This gives
Δ;fst Δ;[[X,Y],Z];fst R;R.
The pure replication wiring satisfies Δ;fst Δ=Δ;snd Δ;rsh. The reshaping wire commutes with parallel components:
rsh;[[X,Y],Z]=[X,[Y,Z]];rsh.
Consequently the left side equals
Δ;snd Δ;[X,[Y,Z]];rsh;fst R;R.
Use the stated associativity premise rsh;fst R;R=snd R;R. The result is
Δ;snd Δ;[X,[Y,Z]];snd R;R,
which is the right side expanded into independent branches. This uses associativity of R and pure product wiring, without assuming commutativity of R or determinism of X,Y,Z.

4. Lift the commutation premise to powers.
[D,D];R=R;D entails [D^c,D^c];R=R;D^c for every c. At c=0 both sides reduce to R. For c+1, split each power into D^c;D, distribute parallel composition over series, apply the original premise to the last [D,D], and apply the induction hypothesis. This generic power-commutation law is a permitted prior result.

5. Prove the general block split by induction on q.
The desired identity is
T_(p+q+1)=Δ;[T_p,T_q;D^(p+1)];R.                  (B)
For q=0, T_0=I reduces the right side to (S) at p.
For the successor q+1, first apply (S) and the induction hypothesis:
```text
T_(p+q+2)
 = Δ;[T_(p+q+1),D^(p+q+2)];R
 = Δ;[Δ;[T_p,T_q;D^(p+1)];R,D^(p+q+2)];R.
```

Since p+q+2=(q+1)+(p+1), write the final power as D^(q+1);D^(p+1). Apply (T) with X=T_p, Y=T_q;D^(p+1), Z=D^(q+1);D^(p+1):
 = Δ;[T_p,Δ;[T_q;D^(p+1),D^(q+1);D^(p+1)];R];R.
Factor the common D^(p+1) inside the second branch and use power commutation:
```text
Δ;[T_q;D^(p+1),D^(q+1);D^(p+1)];R
 = Δ;[T_q,D^(q+1)];[D^(p+1),D^(p+1)];R
 = Δ;[T_q,D^(q+1)];R;D^(p+1)
 = T_(q+1);D^(p+1), by (S).
```

Substitution gives (B) at q+1. This establishes the block-split identity.

6. Justify factoring the two identical half computations.
D^-1;D=I implies D is single-valued: if D x y and D x z, then (D^-1;D) y z, hence y=z. Together with single-valuedness of R and deterministic wiring, this makes every T_m single-valued, by closure under powers, parallel composition and series composition. This generic determinism consequence is a permitted prior result.
For any single-valued U, U;Δ=Δ;[U,U]. The forward direction duplicates one output. In the reverse direction, the two outputs of U from the same input must coincide, so one output witnesses the composition. No totality of U is required. This generic duplication law is a permitted prior result.

7. Complete induction on n.
At n=0, P_0=T_0=I=Q_0.
For the successor, put k=2^n-1. Positivity gives k+1=2^n, and 2^(n+1)-1=k+k+1. Use the reindexing equality and (B) for equal blocks:
```text
P_(n+1)
 = T_(k+k+1)
 = Δ;[T_k,T_k;D^(k+1)];R
 = Δ;[T_k,T_k];snd(D^(k+1));R
 = T_k;Δ;snd(D^(k+1));R, by determinism
 = P_n;Δ;snd(D^(2^n));R
 = Q_n;Δ;snd(D^(2^n));R, by induction
 = Q_(n+1), by definition.
```
