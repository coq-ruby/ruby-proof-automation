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

Definition mapn_zero_f {A B} (x:t A 0) : t B 0 := nil B.

Definition mapn_zero_rf {A B}:
  rel (t A 0) (t B 0) :=
  fun i j => j = mapn_zero_f i.

Definition mapn_zero {A B}:
  rel (t A 0) (t B 0) :=
  fun i j => i = nil A /\ j = nil B.

Fixpoint mapn {A B} (n:nat) (R: rel A B): 
  rel (t A n) (t B n) :=
  match n with
    0 => mapn_zero
  | S p => (apr p)^~1 ; [(mapn p R), R] ; apr p
  end.

Fixpoint mapnl {A B} (n:nat) (R: rel A B): 
  rel (t A n) (t B n) :=
  match n with
    0 => mapn_zero
  | S p => (apl p)^~1 ; [R, (mapnl p R)] ; apl p
  end.

Lemma mapn_zero_series:
  forall A B C,
  mapn_zero (A:=A) (B:=C) = mapn_zero (A:=A) (B:=B); mapn_zero (A:=B) (B:=C).

Lemma mapn_series:
  forall A B C (n:nat) (R: rel A B) (S: rel B C),
  mapn n (R; S) = mapn n R; mapn n S.

Lemma empty_is_nil' : forall A n (v: t A n),
match n return t A n -> Prop with
| O => fun v => v = nil A
| _ => fun _ => True
end v.

Lemma empty_is_nil:
  forall A {a: t A 0},
  a = nil A.

Lemma mapn_id:
  forall A (n:nat),
  mapn n (id A) = id (t A n).

Lemma mapn_conv:
  forall A B (n:nat) (R: rel A B),
  (mapn n R)^~1 = mapn n (R^~1).

Definition rdr_zero {A B}: 
  rel ((t A 0)*B) B :=
  fun i j => snd i = j.

Fixpoint rdr {A B} (n:nat) (R: rel (A*B) B):
  rel (t A n * B) B :=
  match n with
    0 => rdr_zero
  | S p => FST ((apr p)^~1) ; lsh ; SND R ; rdr p R
  end.

Lemma mapn_rdr_id_zero:
  forall A B,
  [mapn_zero(A:=A) (B:=A), id B]; rdr_zero = rdr_zero.

Definition rdl_zero {A B}:
  rel (A * t B 0) A :=
  fun i j => fst i = j.

Fixpoint rdl {A B} (n:nat) (Q: rel (A*B) A):
  rel (A * t B n) A :=
  match n with
    0 => (rdl_zero)
  | S p => SND (apl p)^~1 ; rsh ; FST Q; rdl p Q
  end.

Fixpoint tri {A} (n:nat) (R: rel A A):
  rel (t A n) (t A n) :=
  match n with 
    0 => mapn_zero
  | S p => (apr p)^~1; [tri p R, R^^p]; apr p
end.

Lemma tri_mapn:
  forall A (n:nat) (R: rel A A),
  mapn n R; tri n R = tri n R; mapn n R.

Lemma tri_id:
  forall A (n:nat),
  tri n (id A) = id (t A n).

Require Export rec.

Require Import Arith Lia Eqdep_dec.

Local Open Scope nat_scope.

Lemma S2nM1 : forall n:nat, 2^n = S (2^n - 1).

Lemma Sn2 : forall n:nat, 2 ^ S n = 2^n + 2^n.

Lemma pow2_pos : forall n, 1 <= 2 ^ n.

Definition cast_rel {A} {m n:nat} (H: m = n) : rel (t A m) (t A n) :=
  fun u v => eq_rect m (t A) u n H = v.

Lemma cast_rel_refl : forall A n (H: n = n), cast_rel (A:=A) H = id (t A n).

Lemma cast_rel_chain :
  forall A m n p (H1: m = n) (H2: n = p),
  cast_rel (A:=A) H1 ; cast_rel H2 = cast_rel (eq_trans H1 H2).

Lemma cast_rel_iso :
  forall A m n (H: m = n),
  cast_rel (A:=A) H ; cast_rel (eq_sym H) = id (t A m).

Lemma cast_rel_iso2 :
  forall A m n (H: m = n),
  cast_rel (A:=A) (eq_sym H) ; cast_rel H = id (t A n).

Lemma cast_tri :
  forall A m n (H: m = n) (X: rel A A),
  tri m X ; cast_rel H = cast_rel H ; tri n X.

Definition mfork {A} (n:nat) : rel A (t A n) :=
  fun a v => v = const a n.

Definition apn {A} (p q:nat) : rel (t A p * t A q) (t A (p+q)) :=
  fun u w => append (fst u) (snd u) = w.

Lemma mapn_zero_id :
  forall A, [ @mapn_zero A A , id A ] = id (t A 0 * A).

Lemma tri_one :
  forall A (X: rel A A), tri 1 X = id (t A 1).

Lemma apl_apr_interchange :
  forall A (p:nat),
  FST (apl p) ; apr (S p) = lsh ; SND (@apr A p) ; apl (S p).

Lemma rdl_zero_fst :
  forall A (X: rel A A),
  [X, @mapn_zero A A] ; rdl_zero = rdl_zero ; X.

Lemma shiftin_const :
  forall A (a:A) (q:nat), shiftin a (const a q) = const a (S q).

Lemma mfork_snoc :
  forall A (q:nat), @mfork A (S q) = fork ; [ mfork q , id A ] ; apr q.

Lemma cast_mfork :
  forall A m n (H: m = n), @mfork A m ; cast_rel H = mfork n.

Lemma hd_shiftin :
  forall B (m:nat) (b:B) (u: t B (S m)), hd (shiftin b u) = hd u.

Lemma tl_shiftin :
  forall B (m:nat) (b:B) (u: t B (S m)), tl (shiftin b u) = shiftin b (tl u).

Lemma cons_hd_tl :
  forall B (m:nat) (v: t B (S m)), hd v :: tl v = v.

Lemma fst_snd_comm :
  forall A B C E (X: rel A B) (Y: rel C E),
  FST X ; SND Y = SND Y ; FST X.

Lemma snd_conv :
  forall A B C (X: rel A B), ((@SND A B C X)^~1) = SND (X^~1).

Lemma rdl_S :
  forall A B (m:nat) (Q: rel (A*B) A),
  rdl (S m) Q = (SND (apl m))^~1 ; rsh ; FST Q ; rdl m Q.

Lemma rdl_snoc :
  forall A B (m:nat) (Q: rel (A*B) A),
  rdl (S m) Q = SND ((apr m)^~1) ; rsh ; FST (rdl m Q) ; Q.

Lemma tri_S :
  forall A (n:nat) (X: rel A A),
  tri (S n) X = (apr n)^~1 ; [tri n X, X^^n] ; apr n.

Lemma shiftin_inj :
  forall B (m:nat) (a b: B) (u w: t B m),
  shiftin a u = shiftin b w -> a = b /\ u = w.

Lemma W2 :
  forall A (m:nat),
  @apr A (S m) ; (apl (S m))^~1 ; SND ((apr m)^~1) =
  FST ((apl m)^~1) ; lsh.

Lemma fork_assoc :
  forall A, @fork A ; FST fork = fork ; SND fork ; rsh.

Lemma rsh_para :
  forall A B C E F G (X: rel A B) (Y: rel C E) (Z: rel F G),
  [X, [Y, Z]] ; rsh = rsh ; [[X, Y], Z].

Lemma fst_snd_para :
  forall A B C E (Cx: rel A B) (Z: rel C E),
  FST Cx ; SND Z = [Cx, Z].

Definition det {X Y : Type} (T: rel X Y) : Prop :=
  forall x y z, T x y -> T x z -> y = z.

Lemma det_series :
  forall X Y Z (S: rel X Y) (T: rel Y Z),
  det S -> det T -> det (S ; T).

Lemma det_para :
  forall X Y Z W (S: rel X Y) (T: rel Z W),
  det S -> det T -> det ([S, T]).

Lemma det_id : forall X, det (id X).

Lemma det_mfork : forall X n, det (@mfork X n).

Lemma det_rsh : forall X Y Z, det (@rsh X Y Z).

Lemma det_apr : forall X n, det (@apr X n).

Lemma det_apr1 : forall X n, det ((@apr X n)^~1).

Lemma det_apl1 : forall X n, det ((@apl X n)^~1).

Lemma det_pow : forall X (T: rel X X) c, det T -> det (T ^^ c).

Lemma det_absorb :
  forall X Y (T: rel X Y), det T -> T ; fork = fork ; [T, T].

Section Monitor.

Variable A : Type.

Variable D : rel A A.

Variable R : rel (A*A) A.

Hypothesis D_c2 : D^~1 ; D = id A.

Hypothesis Hpush : [D, D] ; R = R ; D.

Hypothesis Hassoc : rsh ; FST R ; R = SND R ; R.

Hypothesis Rdet : det R.

Definition P (n:nat) : rel A A :=
  mfork (2^n) ; tri (2^n) D ; cast_rel (S2nM1 n) ;
  (apl (2^n - 1))^~1 ; rdl (2^n - 1) R.

Fixpoint Q (n:nat) : rel A A :=
  match n with
  | 0   => id A
  | S p => Q p ; fork ; SND (D ^^ (2^p)) ; R
  end.

Lemma base_wire : mfork 1 ; (apl 0)^~1 ; (@rdl_zero A A) = id A.

Lemma Hpush_pow :
  forall c, [D^^c, D^^c] ; R = R ; D^^c.

Definition PP (m:nat) : rel A A :=
  mfork (S m) ; tri (S m) D ; (apl m)^~1 ; rdl m R.

Lemma PP0 : PP 0 = id A.

Lemma P_as_PP : forall n, P n = PP (2^n - 1).

Lemma Ddet : det D.

Lemma det_tri : forall k, det (tri k D).

Lemma det_rdl : forall k, det (rdl k R).

Lemma det_PP : forall m, det (PP m).

End Monitor.
