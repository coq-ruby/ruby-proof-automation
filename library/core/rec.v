Require Export wire.

Definition mapn_zero_f {A B} (x:t A 0) : t B 0 := nil B.

Definition mapn_zero_rf {A B}:
  rel (t A 0) (t B 0) :=
  fun i j => j = mapn_zero_f i.
(* i = nil A /\ j = nil B *)

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
Proof. intros.
rel_ext.
+ unfold series. unfold mapn_zero. intro.
  destruct H.
  exists (nil B). auto. auto.
+ unfold series. unfold mapn_zero. intro.
  destruct H. destruct H. destruct H0.
  split. auto. auto.
Qed.


Lemma mapn_series:
  forall A B C (n:nat) (R: rel A B) (S: rel B C),
  mapn n (R; S) = mapn n R; mapn n S.
Proof.
intros.
induction n.
- simpl. apply mapn_zero_series.
- simpl.
  series_rewrite_rhs apr_apr1.
  rewrite id_right.
  series_rewrite_rhs_rev para_series.
  rewrite IHn.
  auto.
Qed.

Lemma empty_is_nil' : forall A n (v: t A n),
match n return t A n -> Prop with
| O => fun v => v = nil A
| _ => fun _ => True
end v.
Proof.
destruct v; auto.
Qed.

Lemma empty_is_nil:
  forall A {a: t A 0},
  a = nil A.
Proof. 
intros; apply (empty_is_nil' _ _ a).
Qed.

Lemma mapn_id:
  forall A (n:nat),
  mapn n (id A) = id (t A n).
Proof.
  intros.
  induction n.
- simpl. unfold mapn_zero, id. rel_ext.
  + intros [H1 H2]. rewrite H1. auto.
  + intro. 
    rewrite (empty_is_nil A), (empty_is_nil A (a:=x0)).
    auto.
- simpl. rewrite IHn. rewrite para_id.
  rewrite id_right. rewrite apr1_apr.
  auto.
Qed.

Lemma mapn_conv:
  forall A B (n:nat) (R: rel A B),
  (mapn n R)^~1 = mapn n (R^~1).
Proof.
  intros.
  induction n.
- simpl. unfold mapn_zero, converse.
  rel_ext.
  + intros [H1 H2]. auto.
  + intros [H1 H2]. auto.
- simpl. 
  repeat rewrite series_conv.
  rewrite para_conv.
  rewrite IHn.
  rewrite conv_conv.
  series_reflexivity.
Qed.

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
Proof.
  intros. unfold mapn_zero, id, rdr_zero.
  unfold parallel, series.
  rel_ext.
- intro. destruct H. destruct H. destruct H.
  rewrite H1. auto.
- intro. exists (nil A, x0). split. split.
  destruct x. simpl in H.
  simpl. apply empty_is_nil.
  simpl. auto.
  simpl. auto.
  simpl. auto. 
Qed.

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
Proof.
  intros.
  induction n.
  - simpl. auto.
  - simpl.
    series_rewrite_lhs apr_apr1.
    rewrite id_right.
    series_rewrite_lhs_rev para_series.
    rewrite IHn.
    rewrite pow_left. rewrite <- pow_right.
    series_rewrite_rhs apr_apr1.
    rewrite id_right.
    series_rewrite_lhs para_series. 
    auto.
Qed.

Lemma tri_id:
  forall A (n:nat),
  tri n (id A) = id (t A n).
Proof.
  intros. induction n.
- simpl. unfold mapn_zero, id.
  rel_ext.
  + intros [H1 H2]. rewrite H1, H2. auto.
  + intros. split. 
    apply empty_is_nil. apply empty_is_nil.
- simpl. rewrite IHn.
  rewrite id_pow.
  rewrite para_id.
  rewrite id_right.
  rewrite apr1_apr. auto.
Qed.
