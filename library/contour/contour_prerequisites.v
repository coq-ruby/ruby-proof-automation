Require Export twod.

Lemma snoc_inv:
  forall (A : Type) (p : nat) (u : t A (S p)),
  exists b v, u = shiftin b v.
Proof.
  intros. exists (last u), (shiftout u).
  apply vec_shiftin_last_shiftout.
Qed.

Lemma tri_snoc:
  forall (A : Type) (p : nat) (R : rel A A) (b c : A) (v w : t A p),
  tri (S p) R (shiftin b v) (shiftin c w) <-> tri p R v w /\ (R ^^ p) b c.
Proof.
  intros. simpl. split.
  - intros [k2 [k1 H1 H2] H3].
    destruct k1 as [f0 l0]. destruct k2 as [f1 l1].
    unfold converse, apr in H1. simpl in H1.
    apply vec_shiftin_eq in H1. destruct H1 as [Hl0 Hf0].
    unfold parallel in H2. simpl in H2. destruct H2 as [Ht Hp].
    unfold apr in H3. simpl in H3.
    apply vec_shiftin_eq in H3. destruct H3 as [Hl1 Hf1].
    subst. auto.
  - intros [Ht Hp].
    exists (w, c).
    + exists (v, b).
      * unfold converse, apr. reflexivity.
      * unfold parallel. simpl. auto.
    + unfold apr. reflexivity.
Qed.

Lemma cancel_total:
  forall (A : Type) (R : rel A A),
  R; R^~1 = id A ->
  forall a : A, exists b : A, R a b.
Proof.
  intros A R H a.
  assert (Hc: (R; R^~1) a a) by (rewrite H; reflexivity).
  destruct Hc as [b Hb _]. exists b. exact Hb.
Qed.

Lemma cancel_func:
  forall (A : Type) (R : rel A A),
  R^~1; R = id A ->
  forall k a b : A, R k a -> R k b -> a = b.
Proof.
  intros A R H k a b Ha Hb.
  assert (Hc: (R^~1; R) a b) by (exists k; assumption).
  rewrite H in Hc. exact Hc.
Qed.

Lemma cancel_inj:
  forall (A : Type) (E : rel A A),
  E; E^~1 = id A ->
  forall a b m : A, E a m -> E b m -> a = b.
Proof.
  intros A E H a b m Ha Hb.
  assert (Hc: (E; E^~1) a b) by (exists m; [exact Ha | exact Hb]).
  rewrite H in Hc. exact Hc.
Qed.

Lemma cancel_surj:
  forall (A : Type) (E : rel A A),
  E^~1; E = id A ->
  forall b : A, exists a : A, E a b.
Proof.
  intros A E H b.
  assert (Hc: (E^~1; E) b b) by (rewrite H; reflexivity).
  destruct Hc as [a _ Ha]. exists a. exact Ha.
Qed.

Lemma pow_surj:
  forall (A : Type) (E : rel A A),
  (forall b : A, exists a : A, E a b) ->
  forall (n : nat) (b : A), exists a : A, (E^^n) a b.
Proof.
  intros A E Hs n. induction n; intros b.
  - exists b. reflexivity.
  - destruct (Hs b) as [m Hm].
    destruct (IHn m) as [a Ha].
    exists a. exists m; assumption.
Qed.

Definition conj4 {A B A' B' : Type}
  (R : rel (A * B) (B * A)) (S : rel (B * A) (B' * A')) : rel (A' * B') (B' * A') :=
  swp; S^~1; swp; R; S.

Notation " R \\ S " := (conj4 R S) (at level 41, left associativity).

(* The paired conjugation expands to the concrete wiring pattern. *)
Lemma conj4_pair:
  forall (A B A' B' : Type)
  (R : rel (A * B) (B * A)) (S : rel B B') (T : rel A A'),
  R \\ [S, T] = [T^~1, S^~1]; R; [S, T].
Proof.
  intros A B A' B' R S T.
  unfold conj4. rel_ext.
  - destruct x as [a' b']. destruct x0 as [b1' a1'].
    intros [k4 [k3 [k2 [k1 H1 H2] H3] H4] H5].
    destruct k1 as [b1 a1].
    unfold swp in H1. simpl in H1. destruct H1 as [Ha1 Hb1].
    destruct k2 as [b2 a2].
    unfold converse, parallel in H2. simpl in H2. destruct H2 as [HS HT].
    destruct k3 as [a3 b3].
    unfold swp in H3. simpl in H3. destruct H3 as [Hb3 Ha3].
    destruct k4 as [b4 a4].
    destruct H5 as [HS' HT'].
    subst.
    exists (b4, a4).
    + exists (a3, b3).
      * unfold converse, parallel. simpl. split; assumption.
      * exact H4.
    + split; assumption.
  - destruct x as [a' b']. destruct x0 as [b1' a1'].
    intros [k2 [k1 H1 H2] H3].
    destruct k1 as [a2 b2].
    unfold converse, parallel in H1. simpl in H1. destruct H1 as [HT HS].
    destruct k2 as [b4 a4].
    destruct H3 as [HS' HT'].
    exists (b4, a4); [| split; assumption].
    exists (a2, b2); [| exact H2].
    exists (b2, a2); [| unfold swp; simpl; split; reflexivity].
    exists (b', a').
    + unfold swp. simpl. split; reflexivity.
    + unfold converse, parallel. simpl. split; assumption.
Qed.

