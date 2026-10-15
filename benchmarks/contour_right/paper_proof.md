# Right-grid contour transformation

Let R:A×B→B×A, EA:A→A and EB:B→B be relations. Assume both
cancellation directions for EA and EB, and the cell equality
R=[EA,EB];R;[EB^-1,EA^-1]. Series is ;, parallel is [U,V], beside is ↔,
and E^-k=(E^-1)^k uses relational converse. We prove for all natural m,n:

```text
grid_(m,n) R=snd(triangle_m EB);grid_(m,n)(R;snd EA);
             [(triangle_m EB)^-1,map_n(EA^-m)].
```

Let P=R;snd EA, G_m=grid_(m,n) R, G'_m=grid_(m,n) P,
C=col_n R, M=map_n EA, K_m=map_m EB, Kbar_m=map_m(EB^-1),
T_m=triangle_m EB, Tbar_m=triangle_m(EB^-1),
and L_m=map_n(EA^-m). These are abbreviations for the existing Ruby operators.

Expand paired conjugation of the cell as
R=[EA,EB];R;[EB^-1,EA^-1].
The separately proved grid-conjugation law extends that property uniformly
to the array:
G_m=[M,K_m];G_m;[Kbar_m,M^-1].
We use this previously established outer-grid contour law as a prerequisite.
It follows from the cell equality and the four cancellation assumptions;
it does not insert per-cell factors or triangular boundaries.

Induct on m, including m=0.
At m=0 the row is the horizontal identity through empty vertical vectors,
T_0 and Tbar_0 are identities, and L_0=map_n I=I. Thus the target reduces to
the same empty-row relation on both sides. Do not impose n>0: the generic laws
also cover empty columns and mapped zero-length vectors.

For m+1, assume G_m=snd T_m;G'_m;[Tbar_m,L_m].
First expand the smaller grid and insert the induction hypothesis:

```text
G_m
 = [M,K_m];G_m;[Kbar_m,M^-1]
 = [M,K_m];snd T_m;G'_m;[Tbar_m,L_m];[Kbar_m,M^-1]
 = [M,K_m;T_m];G'_m;[Tbar_m;Kbar_m,L_(m+1)].
```

The last equality is parallel/series exchange. Its final horizontal component
uses M^-1=map_n(EA^-1) and
L_m;M^-1=map_n(EA^-m;EA^-1)=map_n(EA^-(m+1)).
Put alpha=Tbar_m;Kbar_m, beta=L_(m+1), and V=K_m;T_m.
Now continue from the original larger grid to its transformed form:

```text
grid_(m+1,n) R
 = snd(apl_m^-1);(C ↔ G_m);fst apl_m
 = snd(apl_m^-1);
   (C ↔ ([M,V];G'_m;[alpha,beta]));fst apl_m
 = snd(apl_m^-1);
   (C ↔ (fst M;snd V;G'_m;[alpha,beta]));fst apl_m
 = snd(apl_m^-1);
   ((C;snd M) ↔ (snd V;G'_m;[alpha,beta]));fst apl_m
 = snd(apl_m^-1);snd(snd V);
   (col_n P ↔ (G'_m;[alpha,beta]));fst apl_m
 = snd(apl_m^-1);snd(snd V);
   (col_n P ↔ G'_m);[snd alpha,beta];fst apl_m
 = snd T_(m+1);snd(apl_m^-1);
   (col_n P ↔ G'_m);fst apl_m;[Tbar_(m+1),beta]
 = snd T_(m+1);grid_(m+1,n) P;[Tbar_(m+1),L_(m+1)]
 = snd(triangle_(m+1) EB);grid_(m+1,n)(R;snd EA);
   [(triangle_(m+1) EB)^-1,map_n(EA^-(m+1))].
```

The first equality unfolds grid as row of columns and uses the row's standard
prepend wiring, with apl_m joining an element to an m-vector. The next two
substitute the smaller-grid equation and decompose parallel into fst/snd.
The seam exchange law is A↔(fst U;B)=(A;snd U)↔B.
Column/map absorption is col_n R;snd(map_n EA)=col_n(R;snd EA).
Input exchange is A↔(snd V;B)=snd(snd V);(A↔B).
Output exchange is A↔(B;[U,W])=(A↔B);[snd U,W].

The boundary collection step uses the following pair of equalities,
written with explicit typed wires:
apl_m^-1;snd(map_m E;triangle_m E);apl_m=triangle_(m+1) E,
apl_m^-1;snd(triangle_m E;map_m E);apl_m=triangle_(m+1) E.
Both hold for arbitrary E, so use E=EB and E=EB^-1 respectively. The second
also uses the generic map/triangle commutation identity. Interface-wire
cancellation is valid for apl_m. For any such W with W;W^-1=I,
snd(W^-1);snd Q=snd(W^-1;Q;W);snd(W^-1),
[Q,U];fst W=fst W;[W^-1;Q;W,U].
These collect both vector boundaries without altering the middle beside block.
Fold the definition of grid, and use
triangle_m(EB^-1)=(triangle_m EB)^-1 to express the final boundary as a converse.

