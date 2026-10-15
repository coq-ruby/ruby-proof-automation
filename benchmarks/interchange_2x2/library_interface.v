Require Export FunctionalExtensionality.

Require Export PropExtensionality.

Require Export axioms.

Definition rel (A B: Type) := A -> B -> Prop.

Definition series {A B C} 
  (R: rel A B) (S: rel B C):
  rel A C :=
  fun i j => exists2 k, R i k & S k j.

Notation " Q ; R " := (series Q R)
  (at level 40, left associativity).

Definition parallel {A B X Y}
  (R: rel A X) (S: rel B Y):
  rel (A*B) (X*Y) :=
  fun i j => R (fst i) (fst j) /\ S (snd i) (snd j).

Notation " [ Q , R ] " := (parallel Q R)
  (at level 38, left associativity).

Lemma series_assoc:
  forall A B C D (R:rel A B) (S:rel B C) (T:rel C D),
  R;(S;T) = (R;S);T.

Lemma series_congr_left:
  forall A B C (R R': rel A B) (S: rel B C),
  R = R' -> R;S = R';S.

Lemma series_congr_right:
  forall A B C (R: rel A B) (S S': rel B C),
  S = S' -> R;S = R;S'.

Require Export rel.

Definition converse {A B}
  (R: rel A B):
  rel B A :=
  fun i j => R j i.

Notation " R ^~1 " := (converse R)
  (at level 39, left associativity).

Definition id 
  (A:Type): 
  rel A A :=
  fun i j => i=j.

Definition FST {A B C}
  (R: rel A B):
  rel (A*C) (B*C) :=
  [R, id C].

Definition SND {A B C}
  (R: rel A B):
  rel (C*A) (C*B) :=
  [id C, R].

Lemma id_left:
  forall A B (R:rel A B),
  id A; R = R.

Lemma id_right:
  forall A B (R: rel A B),
  R; id B = R.

Lemma id_left_right:
  forall A B (R: rel A B),
  id A; R = R; id B.

Lemma id_conv:
  forall A,
  id A ^~1 = id A.

Fixpoint pow {A} 
  (n:nat) (R: rel A A):
  rel A A :=
  match n with
    0 => id A
  | S p => pow p R ; R
  end.

Notation " R ^^ n " := (pow n R)
  (at level 39, left associativity).

Lemma pow_left:
  forall A (n:nat) (R: rel A A),
  R; R^^n = R ^^ (S n).

Lemma pow_right:
  forall A (n:nat) (R: rel A A),
  R^^n; R = R^^(S n).

Lemma pow_left_right:
  forall A (n:nat) (R: rel A A),
  R; R^^n = R^^n; R.

Lemma pow_add:
  forall A (m n:nat) (R: rel A A),
  R^^m ; R^^n = R^^(m+n).

Lemma id_pow:
  forall A (n:nat),
  id A^^n = id A.

Lemma conv_conv:
  forall A B (R: rel A B),
  (R^~1)^~1 = R.

Lemma series_conv:
  forall A B C (R: rel A B) (S: rel B C),
  (R;S)^~1 = S^~1; R^~1.

Lemma pow_conv:
  forall A (n:nat) (R: rel A A),
  (R^^n)^~1 = (R^~1)^^n.

Lemma para_conv:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S]^~1 = [R^~1, S^~1].

Lemma para_series:
  forall A B C D E F
  (R: rel A B) (S: rel D E) (T: rel B C) (U: rel E F),
  [R;T,S;U] = [R,S]; [T,U].

Lemma para_id:
  forall A B,
  [id A, id B] = id (A*B).

Lemma para_id_left:
  forall A B (R:rel (A*B) B),
  ([id A, id B]; R) = R.

Lemma fst_conv:
  forall A B C (R:rel A B),
  (FST (C:=C) R)^~1 = FST (R^~1).

Lemma fst_series:
  forall A B C D (R: rel A B) (S: rel B C),
  (FST (C:=D) R); (FST S) = FST (R;S).

Lemma snd_series:
  forall A B C D (R:rel A B) (S:rel B C),
  (SND (C:=D) R); SND S =  SND (R; S).

Lemma para_as_series:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S] = FST R; SND S.

Lemma para_as_series2:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S] = SND S; FST R.

Lemma para_snd:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel D E),
  [R, S]; SND T = [R, S; T].

Lemma para_fst:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel B E),
  [R, S]; FST T = [R; T, S].

Lemma snd_para:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel E C),
  SND T; [R, S] = [R, T; S].

Lemma fst_para:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel E A),
  FST T; [R, S] = [T; R, S].

Require Export basic Vector.

Definition pi1 {A B}:
  rel (A*B) A:=
  fun i j => fst i=j.

Definition pi2 {A B}: 
  rel (A*B) B :=
  fun i j => snd i=j.

Definition swp {A B}:
  rel (A*B) (B*A) :=
  fun i j => fst i = snd j /\ snd i = fst j.

Lemma swpswp:
  forall A B,
  swp (A:=A) (B:=B); swp = id (A*B).

Lemma swp_conv:
  forall A B,
  swp^~1 = swp (A:=B) (B:=A).

Lemma swp_para:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S]; swp = swp; [S, R].

Lemma swp_fst_snd:
  forall A B C (R: rel A B),
  swp; FST R = SND R; swp (A:=C) (B:=B).

Definition fork {A}:
  rel A (A*A) :=
  fun i j => match j with
    | (b,c) => i = b /\ i = c
    end.

Lemma fork_pi1:
  forall A, fork; pi1 = id A.

Lemma fork_pi2:
  forall A, fork; pi2 = id A.

Definition apl {A} (n:nat):
  rel (A * t A n) (t A (S n)) :=
  fun i j => fst i :: snd i = j.

Definition apr {A} (n:nat):
  rel (t A n * A) (t A (S n)) :=
  fun i j => shiftin (snd i) (fst i) = j.

Definition lsh {A B C}:
  rel ((A*B)*C) (A*(B*C)) :=
  fun i j => fst(fst i) = fst j /\
    snd(fst i) = fst(snd j) /\
    snd i = snd(snd j).

Definition rsh {A B C}:
  rel (A*(B*C)) ((A*B)*C) :=
  fun i j => fst i = fst(fst j) /\
    fst(snd i) = snd(fst j) /\
    snd(snd i) = snd j.

Lemma lshrsh:
  forall A B C,
  lsh^~1 = rsh (A:=A) (B:=B) (C:=C).

Lemma rshlsh:
  forall A B C,
  rsh^~1 = lsh (A:=A) (B:=B) (C:=C).

Lemma lsh_rsh:
  forall A B C,
  lsh; rsh = id ((A*B)*C).

Lemma rsh_lsh:
  forall A B C,
  rsh; lsh = id (A*(B*C)).

Lemma para_lsh:
  forall A B C D E F (Q:rel A B) (R:rel C D) (S:rel E F),
  [[Q, R], S]; lsh = lsh; [Q, [R, S]].

Lemma para_rsh:
  forall A B C D E F (Q:rel A B) (R:rel C D) (S:rel E F),
  [Q, [R, S]]; rsh = rsh; [[Q, R], S].

Lemma vec_cons_eq:
  forall A (n:nat) (a0 a1: A) (t0 t1: t A n),
  a0:: t0 = a1:: t1 <-> a0=a1 /\ t0=t1.

Lemma apl_apl1:
  forall A (n:nat),
  apl n; (apl n)^~1 = id (A * t A n).

Lemma apl1_apl:
  forall A (n:nat),
  (apl n)^~1; apl n = id (t A (S n)).

Lemma vec_shiftin_eq:
  forall A (n:nat) (a0 a1: A)(t0 t1: t A n),
  shiftin a0 t0 = shiftin a1 t1 <->
  a0 = a1 /\ t0 = t1.

Lemma vec_shiftin_eq' A n (t0 : t A n) :
  match n as n' return t A n' -> Prop with 0 => fun _ => True | S nn =>
      fun t0 => shiftin (last t0) (shiftout t0) = t0 end t0.

Lemma vec_shiftin_eq2 A n (t0 t1 : t A (S n)) :
    t0 = t1 <-> shiftin (last t0) (shiftout t0) = shiftin (last t1) (shiftout t1).

Lemma vec_shiftin_last_shiftout:
  forall A (n:nat) (x: t A (S n)),
  x = shiftin (last x) (shiftout x).

Lemma apr_apr1:
  forall A (n:nat),
  apr n; (apr n)^~1 = id (t A n * A).

Lemma apr1_apr:
  forall A (n:nat),
  (apr n)^~1; apr n = id (t A (S n)).

Require Export wire.

Definition beside {A B C D E F G}
  (R: rel (A*B) (D*G)) (S: rel (G*C) (E*F)) :=
  rsh; FST R; lsh; SND S; rsh.

Definition beside_pw {A B C D E F G}
  (R: rel (A*B) (D*G)) (S: rel (G*C) (E*F)):
  rel (A*(B*C)) ((D*E)*F) :=
  fun '(a, (b, c)) '((d, e), f) =>
    exists2 g, R (a,b) (d,g) & S (g,c) (e,f).

Lemma beside_dual:
  forall A B C D E F G 
  (R: rel (A*B) (D*G)) (S: rel (G*C) (E*F)),
  beside R S = beside_pw R S.

Notation " R <--> S " := (beside R S)
  (at level 39, left associativity) : function_scope.

Definition below {A B C D E F G}
  (R: rel (A*G) (D*E)) (S: rel (B*C) (G*F)) :=
  lsh; SND S; rsh; FST R; lsh.

Definition below_pw {A B C D E F G}
  (R: rel (A*G) (D*E)) (S: rel (B*C) (G*F)) :=
  fun '((a, b), c) '(d, (e, f)) =>
    exists2 g, R (a,g) (d,e) & S (b,c) (g,f).

Lemma below_dual:
  forall A B C D E F G 
  (R: rel (A*G) (D*E)) (S: rel (B*C) (G*F)),
  below R S = below_pw R S.

Notation " R <||> S " := (below R S)
  (at level 39, left associativity) : function_scope.
