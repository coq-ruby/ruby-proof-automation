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
  
Ltac unfold_rels :=
  unfold series, converse, parallel, id, FST, SND.

Lemma id_left:
  forall A B (R:rel A B),
  id A; R = R.
Proof.
  intros.
  unfold_rels.
  rel_ext.
  - intros [c ? ?]. rewrite H. auto.
  - eauto.
Qed.

Lemma id_right:
  forall A B (R: rel A B),
  R; id B = R.
Proof.
  intros.
  unfold_rels.
  rel_ext. 
  - intros [c ? ?]. rewrite <- H0. eauto.
  - eauto.
Qed.

Lemma id_left_right:
  forall A B (R: rel A B),
  id A; R = R; id B.
Proof.
  intros.
  rewrite id_left, id_right.
  auto.
Qed.

Lemma id_conv:
  forall A,
  id A ^~1 = id A.
Proof.
  intros.
  unfold_rels.
  rel_ext.
  - auto.
  - auto.
Qed.

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
Proof.
  intros.
  induction n.
  simpl. 
  rewrite id_left. rewrite id_right. auto.
  simpl. rewrite series_assoc.
  rewrite IHn.
  auto.
Qed.

Lemma pow_right:
  forall A (n:nat) (R: rel A A),
  R^^n; R = R^^(S n).
Proof. auto. Qed.

Lemma pow_left_right:
  forall A (n:nat) (R: rel A A),
  R; R^^n = R^^n; R.
Proof.
  intros.
  rewrite pow_left.
  rewrite <- pow_right.
  auto.
Qed.

Lemma pow_add:
  forall A (m n:nat) (R: rel A A),
  R^^m ; R^^n = R^^(m+n).
Proof.
  intros.
  induction m.
  - simpl. rewrite id_left. auto.
  - simpl. rewrite <- series_assoc.
    rewrite pow_left_right.
    rewrite series_assoc.
    rewrite IHm. auto.
Qed.

Lemma id_pow:
  forall A (n:nat),
  id A^^n = id A.
Proof.
  intros. induction n.
- simpl. auto.
- simpl. rewrite IHn.
  rewrite id_right.
  auto.
Qed.

Lemma conv_conv:
  forall A B (R: rel A B),
  (R^~1)^~1 = R.
Proof.
  intros.
  unfold converse.
  rel_ext.
  auto. auto.
Qed.

Lemma series_conv:
  forall A B C (R: rel A B) (S: rel B C),
  (R;S)^~1 = S^~1; R^~1.
Proof.
  intros.
  unfold series. unfold converse.
  rel_ext.
  - intro. destruct H as [k H1 H2].
    exists k. auto. auto.
  - intro. destruct H as [k H1 H2].
    exists k. auto. auto.
Qed.

Lemma pow_conv:
  forall A (n:nat) (R: rel A A),
  (R^^n)^~1 = (R^~1)^^n.
Proof.
  intros.
  induction n.
  - simpl. apply id_conv.
  - simpl. rewrite series_conv.
    rewrite IHn.
    rewrite pow_left. rewrite pow_right. auto.
Qed.

Lemma para_conv:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S]^~1 = [R^~1, S^~1].
Proof.
  intros.
  unfold_rels.
  rel_ext.
  destruct x. destruct x0.
  - intro. simpl in H. destruct H.
    simpl. auto.
  - intro. simpl in H. destruct H.
    simpl. auto.
Qed.

Lemma para_series:
  forall A B C D E F
  (R: rel A B) (S: rel D E) (T: rel B C) (U: rel E F),
  [R;T,S;U] = [R,S]; [T,U].
Proof.
  intros.
  unfold_rels.
  rel_ext.
  - intro. destruct H as [H1 H2].
    destruct H1 as [b H11 H12].
    destruct H2 as [e H21 H22].
    exists (b, e). simpl. auto.
    simpl. auto.
  - intro.
    destruct H as [be H1 H2].
    destruct H1 as [H11 H12].
    destruct H2 as [H21 H22].
    destruct be.
    split.
    + exists b. auto. auto.
    + exists e. auto. auto.
Qed.

Lemma para_id:
  forall A B,
  [id A, id B] = id (A*B).
Proof.
intros.
rel_ext.
- unfold id. unfold parallel.
  destruct x. destruct x0. simpl. intro.
  destruct H. rewrite H. rewrite H0. auto.
- unfold id. unfold parallel.
  destruct x. destruct x0. intro.
  injection H. simpl. auto.
Qed.

Lemma para_id_left:
  forall A B (R:rel (A*B) B),
  ([id A, id B]; R) = R.
Proof.
intros.
rewrite para_id.
rewrite id_left.
auto.
Qed.

Lemma fst_conv:
  forall A B C (R:rel A B),
  (FST (C:=C) R)^~1 = FST (R^~1).
Proof.
  intros.
  unfold_rels.
  rel_ext.
  - intro. destruct H. split.
    + auto.
    + unfold id. auto.
  - intro. destruct H. split.
    + auto.
    + unfold id. auto.
Qed.

Lemma fst_series:
  forall A B C D (R: rel A B) (S: rel B C),
  (FST (C:=D) R); (FST S) = FST (R;S).
Proof.
  intros.
  unfold_rels.
  rel_ext.
  - intro. destruct H as [bd H1 H2]. destruct bd. 
    simpl in H1. simpl in H2.
    destruct H1 as [H11 H12]. destruct H2 as [H21 H22]. split.
    + exists b. auto. auto.
    + unfold id in H12. unfold id in H22. unfold id. rewrite H12. auto.
  - intro. destruct H. destruct H as [b H1 H2]. 
    destruct x. destruct x0.
    simpl in H0. simpl in H1. simpl in H2.
    exists (b, d). split.
    + auto.
    + simpl. unfold id. auto.
    + split.
      * simpl. auto.
      * simpl. unfold id. auto.
Qed.

Lemma snd_series:
  forall A B C D (R:rel A B) (S:rel B C),
  (SND (C:=D) R); SND S =  SND (R; S).
Proof.
  intros.
  unfold SND.
  rewrite <- para_series.
  rewrite id_right.
  auto.
Qed.

Lemma para_as_series:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S] = FST R; SND S.
Proof.
  intros.
  unfold FST. unfold SND.
  rewrite <- para_series.
  rewrite id_left. rewrite id_right. auto.
Qed.

Lemma para_as_series2:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S] = SND S; FST R.
Proof.
  intros.
  unfold FST. unfold SND.
  rewrite <- para_series.
  rewrite id_left. rewrite id_right. auto.
Qed.

Lemma para_snd:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel D E),
  [R, S]; SND T = [R, S; T].
Proof.
  intros.
  unfold SND.
  rewrite <- para_series.
  rewrite id_right. auto.
Qed.

Lemma para_fst:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel B E),
  [R, S]; FST T = [R; T, S].
Proof.
  intros.
  unfold FST.
  rewrite <- para_series.
  rewrite id_right. auto.
Qed.

Lemma snd_para:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel E C),
  SND T; [R, S] = [R, T; S].
Proof.
  intros.
  unfold SND.
  rewrite <- para_series.
  rewrite id_left. auto.
Qed.

Lemma fst_para:
  forall A B C D E (R: rel A B) (S: rel C D) (T: rel E A),
  FST T; [R, S] = [T; R, S].
Proof.
  intros.
  unfold FST.
  rewrite <- para_series.
  rewrite id_left. auto.
Qed.

(* Targeted reverse rewrites for the para/fst/snd family.
   T is always the component being moved (factored out or absorbed).
   Use these when multiple [_,_] patterns exist and plain rewrite
   targets the wrong one.

   snd_para_at Q  :  [R, T; S]  →  SND T; [R, S]
   fst_para_at Q  :  [T; R, S]  →  FST T; [R, S]
   para_snd_at Q  :  [R, S; T]  →  [R, S]; SND T
   para_fst_at Q  :  [R; T, S]  →  [R, S]; FST T   *)

Ltac snd_para_at T := rewrite <- (snd_para _ _ _ _ _ _ _ T).
Ltac fst_para_at T := rewrite <- (fst_para _ _ _ _ _ _ _ T).
Ltac para_snd_at T := rewrite <- (para_snd _ _ _ _ _ _ _ T).
Ltac para_fst_at T := rewrite <- (para_fst _ _ _ _ _ _ _ T).
