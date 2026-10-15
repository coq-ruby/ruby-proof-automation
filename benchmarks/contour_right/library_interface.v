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

Require Export basic.

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

Require Export wire Vector.

Definition apl {A} (n:nat):
  rel (A * t A n) (t A (S n)) :=
  fun i j => fst i :: snd i = j.

Definition apr {A} (n:nat):
  rel (t A n * A) (t A (S n)) :=
  fun i j => shiftin (snd i) (fst i) = j.

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

Lemma shiftout_shiftin: forall A n (a: A) (v: t A n),
  shiftout (shiftin a v) = v.

Lemma last_shiftin: forall A n (a: A) (v: t A n),
  last (shiftin a v) = a.

Lemma hd_shiftin: forall A n (a: A) (v: t A (S n)),
  hd (shiftin a v) = hd v.

Lemma tl_shiftin: forall A n (a: A) (v: t A (S n)),
  tl (shiftin a v) = shiftin a (tl v).

Require Export wire_rec.

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

Lemma beside_comp:
  forall X (A B C D E F: rel X X)
  (R S: rel (X*X) (X*X)),
  [A,[B,C]]; (R <--> S); [[D,E],F] =
  ([A,B];R;FST D) <--> (SND C; S; [E,F]).

Lemma below_comp:
  forall X (A B C D E F: rel X X)
  (R S: rel (X*X) (X*X)),
  [[A,B],C]; (R <||> S); [D,[E,F]] =
  (FST A; R; [D,E]) <||> ([B,C]; S; SND F).

Definition rsh2 {A B C} :=
  [id A, id B] <--> [id B, id C].

Lemma rsh_dual:
  forall A B C, rsh (A:=A) (B:=B) (C:=C) = rsh2.

Definition lsh2 {A B C} :=
  [id A, id B] <||> [id B, id C].

Lemma lsh_dual:
  forall A B C, lsh (A:=A) (B:=B) (C:=C) = lsh2.

Lemma beside_fst:
  forall A B C D E F G H (R: rel (A*B) (C*D)) (S: rel (E*F) (G*H)) (T: rel D E),
  R <--> (FST T; S) = (R; SND T) <--> S.

Lemma beside_snd:
  forall A B C D E F G H (R: rel (A*B) (C*D)) (S: rel (D*E) (F*G)) (T: rel H E),
  R <--> (SND T; S) = SND (SND T); (R <--> S).

Lemma beside_block_para:
  forall A B C D E F G H I
  (R: rel (A*B) (C*D)) (S: rel (D*E) (F*G))
  (T: rel F H) (U: rel G I),
  R <--> (S; [T, U]) = (R <--> S); [SND T, U].

Definition row_zero {A B C}:
  rel (A*t B 0) (t C 0*A):=
  fun i j => fst i = snd j.

Fixpoint row {A B C} 
  (n:nat) (R: rel (A*B) (C*A)) :=
  match n with
    0 => row_zero
  | S p => SND ((apl p)^~1); R <--> (row p R); FST (apl p)
end.

Fixpoint row2 {A B C} 
  (n:nat) (R: rel (A*B) (C*A)) :=
  match n with
    0 => row_zero
  | S p => SND ((apr p)^~1); (row2 p R) <--> R; FST (apr p)
end.

Fixpoint row_pw {A B C} (n:nat) (R: rel (A*B) (C*A)):
  rel (A * t B n) (t C n * A) :=
  match n with
  | 0 => row_zero
  | S p => fun '(a, v) '(w, a_out) =>
      exists2 g, R (a, hd v) (hd w, g) & 
        row_pw p R (g, tl v) (tl w, a_out)
  end.

Fixpoint row_pw2 {A B C} (n:nat) (R: rel (A*B) (C*A)):
  rel (A * t B n) (t C n * A) :=
  match n with
  | 0 => row_zero
  | S p => fun '(a, v) '(w, a_out) =>
      exists2 g, row_pw2 p R (a, shiftout v) (shiftout w, g) & 
        R (g, last v) (last w, a_out)
  end.

Lemma row_dual:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row n R = row_pw n R.

Lemma row2_dual2:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row2 n R = row_pw2 n R.

Lemma row_pw_snoc:
  forall A B C (n:nat) (R: rel (A*B) (C*A))
  (a a_out: A) (v: t B n) (b: B) (w: t C n) (c: C),
  row_pw (S n) R (a, shiftin b v) (shiftin c w, a_out) <->
  exists2 g, row_pw n R (a, v) (w, g) & R (g, b) (c, a_out).

Lemma row_pw_equiv:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row_pw n R = row_pw2 n R.

Lemma row2_dual:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row2 n R = row_pw n R.

Lemma row_row2:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row n R = row2 n R.

Definition col_zero {A B C}:
  rel (t A 0*B) (B*t C 0) :=
  fun i j => snd i = fst j.

Fixpoint col {A B C} 
  (n:nat) (R: rel (A*B) (B*C)) :=
  match n with
    0 => col_zero
  | S p => FST ((apl p)^~1); R <||> (col p R); SND (apl p)
  end.

Fixpoint col2 {A B C} 
  (n:nat) (R: rel (A*B) (B*C)) :=
  match n with
    0 => col_zero
  | S p => FST ((apr p)^~1); (col2 p R) <||> R; SND(apr p)
  end.

Fixpoint col_pw {A B C} (n:nat) (R: rel (A*B) (B*C)):
  rel (t A n * B) (B * t C n) :=
  match n with
  | 0 => col_zero
  | S p => fun '(v, b) '(b_out, w) =>
      exists2 g, R (hd v, g) (b_out, hd w) &
        col_pw p R (tl v, b) (g, tl w)
  end.

Fixpoint col_pw2 {A B C} (n:nat) (R: rel (A*B) (B*C)):
  rel (t A n * B) (B * t C n) :=
  match n with
  | 0 => col_zero
  | S p => fun '(v, b) '(b_out, w) =>
      exists2 g, R (last v, b) (g, last w) &
        col_pw2 p R (shiftout v, g) (b_out, shiftout w)
  end.

Lemma col_dual:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col n R = col_pw n R.

Lemma col2_dual2:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col2 n R = col_pw2 n R.

Lemma col_pw_snoc:
  forall A B C (n:nat) (R: rel (A*B) (B*C))
  (b b_out: B) (v: t A n) (a: A) (w: t C n) (c: C),
  col_pw (S n) R (shiftin a v, b) (b_out, shiftin c w) <->
  exists2 g, R (a, b) (g, c) & col_pw n R (v, g) (b_out, w).

Lemma col_pw_equiv:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col_pw n R = col_pw2 n R.

Lemma col2_dual:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col2 n R = col_pw n R.

Lemma col_col2:
  forall A B C (n:nat) (R: rel (A*B) (B*C)),
  col n R = col2 n R.

Definition dstl {A B} (n:nat):=
  row n (fork(A:=A*B); SND pi1); pi1.

Definition dstr {A B} (n:nat):=
  col n (fork(A:=A*B); FST pi2); pi2.

Fixpoint mapn_pw {A B} (n:nat) (R: rel A B): rel (t A n) (t B n) :=
  match n with
  | 0 => mapn_zero
  | S p => fun va wb => R (hd va) (hd wb) /\ mapn_pw p R (tl va) (tl wb)
  end.

Fixpoint mapn_pw2 {A B} (n:nat) (R: rel A B): rel (t A n) (t B n) :=
  match n with
  | 0 => mapn_zero
  | S p => fun va wb => 
      R (last va) (last wb) /\ mapn_pw2 p R (shiftout va) (shiftout wb)
  end.

Lemma mapn_dual2:
  forall A B (n:nat) (R: rel A B),
  mapn n R = mapn_pw2 n R.

Lemma mapn_pw_snoc:
  forall A B (n:nat) (R: rel A B) (a: A) (b: B) (va: t A n) (wb: t B n),
  mapn_pw (S n) R (shiftin a va) (shiftin b wb) <->
  R a b /\ mapn_pw n R va wb.

Lemma mapn_pw_equiv:
  forall A B (n:nat) (R: rel A B),
  mapn_pw n R = mapn_pw2 n R.

Lemma mapn_dual:
  forall A B (n:nat) (R: rel A B),
  mapn n R = mapn_pw n R.

Lemma col_pw_snd_mapn_pw:
  forall A B C (n:nat) (R: rel (A*B) (B*A)) (S: rel A C)
    va b b_out wc,
  (exists wa, col_pw n R (va, b) (b_out, wa) /\ mapn_pw n S wa wc)
  <-> col_pw n (R; SND S) (va, b) (b_out, wc).

Lemma col_snd_mapn:
  forall A B C (n:nat) (R: rel (A*B) (B*A)) (S: rel A C),
  col n R; SND (mapn n S) = col n (R; SND S).

Definition grid {A B} 
  (m:nat) (n:nat) (R: rel (A*B) (B*A)):=
  row m (col n R).

Require Export twod.

Lemma snoc_inv:
  forall (A : Type) (p : nat) (u : t A (S p)),
  exists b v, u = shiftin b v.

Lemma tri_snoc:
  forall (A : Type) (p : nat) (R : rel A A) (b c : A) (v w : t A p),
  tri (S p) R (shiftin b v) (shiftin c w) <-> tri p R v w /\ (R ^^ p) b c.

Lemma cancel_total:
  forall (A : Type) (R : rel A A),
  R; R^~1 = id A ->
  forall a : A, exists b : A, R a b.

Lemma cancel_func:
  forall (A : Type) (R : rel A A),
  R^~1; R = id A ->
  forall k a b : A, R k a -> R k b -> a = b.

Lemma cancel_inj:
  forall (A : Type) (E : rel A A),
  E; E^~1 = id A ->
  forall a b m : A, E a m -> E b m -> a = b.

Lemma cancel_surj:
  forall (A : Type) (E : rel A A),
  E^~1; E = id A ->
  forall b : A, exists a : A, E a b.

Lemma pow_surj:
  forall (A : Type) (E : rel A A),
  (forall b : A, exists a : A, E a b) ->
  forall (n : nat) (b : A), exists a : A, (E^^n) a b.

Definition conj4 {A B A' B' : Type}
  (R : rel (A * B) (B * A)) (S : rel (B * A) (B' * A')) : rel (A' * B') (B' * A') :=
  swp; S^~1; swp; R; S.

Notation " R \\ S " := (conj4 R S) (at level 41, left associativity).

Lemma conj4_pair:
  forall (A B A' B' : Type)
  (R : rel (A * B) (B * A)) (S : rel B B') (T : rel A A'),
  R \\ [S, T] = [T^~1, S^~1]; R; [S, T].

Require Export contour_prerequisites.

Lemma mapn_pw_total : forall A (E:rel A A),
 (forall a, exists b, E a b) -> forall n (v:t A n), exists w, mapn_pw n E v w.

Lemma cell_transport : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA^~1; EA = id A -> EB^~1; EB = id B ->
 R = [EA,EB]; R; [EB^~1,EA^~1] ->
 forall a b c d a1 b1 c1 d1,
 EA a a1 -> EB b b1 -> EB c c1 -> EA d d1 ->
 (R (a,b) (c,d) <-> R (a1,b1) (c1,d1)).

Lemma col_transport : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA; EA^~1 = id A -> EA^~1; EA = id A ->
 EB; EB^~1 = id B -> EB^~1; EB = id B ->
 R = [EA,EB]; R; [EB^~1,EA^~1] ->
 forall n (va va1 vb vb1:t A n) b b1 c c1,
 mapn_pw n EA va va1 -> mapn_pw n EA vb vb1 -> EB b b1 -> EB c c1 ->
 (col_pw n R (va,b) (c,vb) <-> col_pw n R (va1,b1) (c1,vb1)).

Lemma col_conjugation : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA; EA^~1 = id A -> EA^~1; EA = id A ->
 EB; EB^~1 = id B -> EB^~1; EB = id B ->
 R = [EA,EB]; R; [EB^~1,EA^~1] -> forall n,
 col n R = [mapn n EA,EB]; col n R; [EB^~1,(mapn n EA)^~1].

Lemma mapn_power : forall A (E:rel A A) n m,
 (mapn n E)^^m = mapn n (E^^m).

Lemma mapn_cancellation : forall A (E:rel A A),
 E;E^~1 = id A -> forall n,
 mapn n E; (mapn n E)^~1 = id (t A n).

Require Export contour_prerequisites.

Lemma parallel_power:
  forall A B (P : rel A A) (Q : rel B B) n,
  [P,Q]^^n = [P^^n,Q^^n].

Lemma power_cancellation:
  forall A (P Q : rel A A), P;Q = id A ->
  forall n, P^^n;Q^^n = id A.

Lemma inverse_power_extend:
  forall A (P Q : rel A A), P;Q = id A ->
  forall n, Q^^n = P;Q^^(S n).

Lemma conjugation_power:
  forall A B (L : rel A A) (M : rel B B) (P : rel A B),
  P = L;P;M -> forall n, P = L^^n;P;M^^n.

Lemma triangle_converse:
  forall A (P : rel A A) n,
  (tri n P)^~1 = tri n (P^~1).

Lemma row_append:
  forall A B C (P : rel (A*B) (C*A)) n,
  row (S n) P =
  SND ((apr n)^~1); (row n P <--> P); FST (apr n).

Lemma beside_boundary_exchange:
  forall A B C D E
  (P : rel (A*B) (C*A)) (Q : rel (A*D) (E*A))
  (U : rel B B) (V : rel C C) (H K N : rel A A)
  (L : rel D D) (M : rel E E),
  (SND U;P;[V,H]) <--> ([K,L];Q;[M,N]) =
  SND ([U,L]); (P <--> (FST (H;K);Q)); [[V,M],N].

Lemma beside_final_factor:
  forall A B C D E F G H
  (P : rel (A*B) (C*D)) (Q : rel (D*E) (F*G)) (U : rel G H),
  (P <--> Q); SND U = P <--> (Q;SND U).

Lemma interface_input:
  forall A X Y (W : rel X Y) (P : rel X X),
  W;W^~1 = id X ->
  SND (C:=A) (W^~1); SND P = SND (W^~1;P;W); SND (W^~1).

Lemma interface_output:
  forall X Y A B (W : rel X Y) (P : rel X X) (Q : rel A B),
  W;W^~1 = id X ->
  [P,Q];FST W = FST W;[W^~1;P;W,Q].

Require Export grid_helpers equational_helpers.

Lemma row_uniform_transport : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA;EA^~1=id A -> EA^~1;EA=id A ->
 EB;EB^~1=id B -> EB^~1;EB=id B ->
 R=[EA,EB];R;[EB^~1,EA^~1] ->
 forall m a a1 c c1 (v v1 w w1:t B m),
 EA a a1 -> EA c c1 -> mapn_pw m EB v v1 -> mapn_pw m EB w w1 ->
 (row_pw m R (a,v) (w,c) <-> row_pw m R (a1,v1) (w1,c1)).

Lemma row_uniform_conjugation : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA;EA^~1=id A -> EA^~1;EA=id A ->
 EB;EB^~1=id B -> EB^~1;EB=id B ->
 R=[EA,EB];R;[EB^~1,EA^~1] -> forall m,
 row m R = [EA,mapn m EB];row m R;[(mapn m EB)^~1,EA^~1].

Lemma grid_conjugation : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA;EA^~1=id A -> EA^~1;EA=id A ->
 EB;EB^~1=id B -> EB^~1;EB=id B ->
 R=[EA,EB];R;[EB^~1,EA^~1] -> forall m n,
 grid m n R = [mapn n EA,mapn m EB];grid m n R;
 [(mapn m EB)^~1,(mapn n EA)^~1].

Lemma map_triangle_snoc : forall A (E:rel A A) m b c (v w:t A m),
 (mapn (S m) E;tri (S m) E) (shiftin b v) (shiftin c w) <->
 (mapn m E;tri m E) v w /\ (E^^(S m)) b c.

Lemma triangle_cons : forall A (E:rel A A) m b c (v w:t A m),
 tri (S m) E (b::v) (c::w) <->
 b=c /\ (mapn m E;tri m E) v w.

Lemma triangle_prepend : forall A (E:rel A A) m,
 tri (S m) E = (apl m)^~1;SND (mapn m E;tri m E);apl m.

Lemma triangle_prepend_right : forall A (E:rel A A) m,
 tri (S m) E = (apl m)^~1;SND (tri m E;mapn m E);apl m.

Lemma grid_step : forall A B (R:rel (A*B) (B*A)) m n,
 grid (S m) n R = SND ((apl m)^~1);
 (col n R <--> grid m n R);FST (apl m).
