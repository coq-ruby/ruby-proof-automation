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

Ltac destruct_prods :=
  repeat match goal with
  | [ x : _ * _ |- _ ] => destruct x
  end.

Lemma swpswp:
  forall A B,
  swp (A:=A) (B:=B); swp = id (A*B).
Proof.
intros.
apply functional_extensionality. intros.
destruct x as [a0 b0].
apply functional_extensionality. intros.
destruct x as [a1 b1].
apply propositional_extensionality. split.
- unfold swp. unfold series. unfold id. simpl.
  intros.
  destruct H as [k H0 H1].
  destruct k as [b a]. simpl in H0. simpl in H1.
  destruct H0. destruct H1. 
  rewrite H. rewrite H0.
  rewrite H1. rewrite H2. auto.
- unfold swp. unfold series. unfold id. simpl.
  intros. 
  exists (b0, a0). simpl. auto.
  simpl. injection H. auto.
Qed.

Lemma swp_conv:
  forall A B,
  swp^~1 = swp (A:=B) (B:=A).
Proof.
  intros. unfold swp, converse. rel_ext.
- intros [H1 H2]. auto.
- intros [H1 H2]. auto.
Qed.

Lemma swp_para:
  forall A B C D (R: rel A B) (S: rel C D),
  [R, S]; swp = swp; [S, R].
Proof.
  intros.
  unfold swp, parallel, series.
  rel_ext. destruct x; destruct x0; simpl.
  - intros [k [H1 H2] [H3 H4]].
    exists (c, a). split; auto.
    simpl.
    rewrite <- H3, <- H4. 
    split; auto.
- destruct x; destruct x0.
  intros [k [H1 H2] [H3 H4]].
  exists (b, d). split. 
  + rewrite H1; auto.
  + rewrite H2; auto.
  + split. auto. auto.
Qed.

Lemma swp_fst_snd:
  forall A B C (R: rel A B),
  swp; FST R = SND R; swp (A:=C) (B:=B).
Proof.
  intros.
  unfold FST, SND.
  rewrite swp_para.
  auto.
Qed.

Definition fork {A}:
  rel A (A*A) :=
  fun i j => match j with
    | (b,c) => i = b /\ i = c
    end.
    
Lemma fork_pi1:
  forall A, fork; pi1 = id A.
Proof.
  intros.
  unfold fork, pi1, id, series.
  rel_ext.
- intros [k H1 H2]. 
  destruct k. destruct H1. 
  subst. auto.
- intro. exists (x, x0).
  auto. simpl. auto.
Qed.

Lemma fork_pi2:
  forall A, fork; pi2 = id A.
Proof.
  intros.
  unfold fork, pi2, id, series.
  rel_ext.
- intros [k H1 H2].
  destruct k. destruct H1. subst.
  auto.
- intro. exists (x, x0).
  auto. simpl. auto.
Qed.

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
Proof.
  intros.
  unfold converse.
  unfold lsh. unfold rsh.
  rel_ext.
  - intros. destruct H. destruct H0. auto.
  - intros. destruct H. destruct H0. auto.
Qed.

Lemma rshlsh:
  forall A B C,
  rsh^~1 = lsh (A:=A) (B:=B) (C:=C).
Proof.
  intros.
  unfold converse.
  unfold lsh. unfold rsh.
  rel_ext.
  - intros. destruct H. destruct H0. auto.
  - intros. destruct H. destruct H0. auto.
Qed.

Lemma lsh_rsh:
  forall A B C,
  lsh; rsh = id ((A*B)*C).
Proof.
  intros.
  unfold lsh, rsh, series.
  rel_ext.
  destruct x, x0. destruct p, p0.
- intros [k [H1 [H2 H3]] [H4 [H5 H6]]].
  unfold id. simpl in *. subst. auto.
- unfold id. intro. subst. 
  destruct x0. destruct p.
  exists (a, (b, c)).
  simpl. auto.
  simpl. auto.
Qed.

Lemma rsh_lsh:
  forall A B C,
  rsh; lsh = id (A*(B*C)).
Proof.
  intros.
  unfold lsh, rsh, series.
  rel_ext.
  destruct x, x0. destruct p, p0.
  - intros [k [H1 [H2 H3]] [H4 [H5 H6]]].
    unfold id. simpl in *. subst. auto.
  - unfold id. intro. subst.
    destruct x0. destruct p.
    exists ((a, b), c).
    simpl. auto.
    simpl. auto.
Qed.


Lemma para_lsh:
  forall A B C D E F (Q:rel A B) (R:rel C D) (S:rel E F),
  [[Q, R], S]; lsh = lsh; [Q, [R, S]].
Proof.
  intros.
  apply functional_extensionality. intros.
  destruct x. destruct p.
  apply functional_extensionality. intros.
  destruct x. destruct p.
  apply propositional_extensionality. split.
- unfold lsh. unfold series. unfold parallel. simpl.
  intros. destruct H as [k H0 H1].
  destruct k. destruct p.
  simpl in H0. simpl in H1.
  exists (a, (c, e)). simpl. auto.
  simpl. destruct H1 as [H1 H2]. destruct H2 as [H2 H3].
  rewrite <- H1; rewrite <- H2; rewrite <- H3.
  destruct H0. destruct H. eauto.
- unfold lsh; unfold series; unfold parallel. simpl.
  intros. destruct H as [k H0 H1].
  destruct k. destruct p.
  simpl in H0; simpl in H1.
  exists (b, d, f); simpl.
  destruct H0. destruct H0.
  rewrite H; rewrite H0; rewrite H2.
  destruct H1. destruct H3. eauto.
  auto.
Qed.

Lemma para_rsh:
  forall A B C D E F (Q:rel A B) (R:rel C D) (S:rel E F),
  [Q, [R, S]]; rsh = rsh; [[Q, R], S].
Proof.
  intros.
  apply functional_extensionality. intros.
  destruct x. destruct p.
  apply functional_extensionality. intros.
  destruct x. destruct p.
  apply propositional_extensionality. split.
- unfold rsh; unfold series; unfold parallel. simpl.
  intros. destruct H as [k H0 H1].
  destruct k. destruct p.
  simpl in H0; simpl in H1.
  exists (a, c, e). simpl. auto.
  simpl. destruct H1 as [H1 H2]. destruct H2 as [H2 H3].
  rewrite <- H1; rewrite <- H2; rewrite <- H3.
  destruct H0. destruct H0. eauto.
- unfold rsh; unfold series; unfold parallel. simpl.
  intros. destruct H as [k H0 H1].
  destruct k. destruct p.
  simpl in H0; simpl in H1.
  exists (b, (d, f)); simpl.
  destruct H0. destruct H0.
  rewrite H; rewrite H0; rewrite H2.
  destruct H1. destruct H1. eauto.
  auto.
Qed.

