Require Export basic Vector.
Export VectorNotations.

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

Lemma vec_cons_eq:
  forall A (n:nat) (a0 a1: A) (t0 t1: t A n),
  a0:: t0 = a1:: t1 <-> a0=a1 /\ t0=t1.
Proof.
intros. split.
- intro. apply cons_inj. auto.
- intro. destruct H.
  rewrite H; rewrite H0.
  auto.
Qed.

Lemma apl_apl1:
  forall A (n:nat),
  apl n; (apl n)^~1 = id (A * t A n).
Proof.
intros. 
apply functional_extensionality. intros.
apply functional_extensionality. intros.
destruct x. destruct x0.
apply propositional_extensionality. split.
- unfold apl; unfold series; unfold converse.
  intros. simpl in H. destruct H as [k H0].
  unfold id.
  rewrite <- H in H0.
  rewrite vec_cons_eq in H0.
  apply pair_equal_spec. auto.
- unfold id; unfold apl; unfold series; unfold converse.
  simpl. intros.
  exists (a:: t). auto.
  apply pair_equal_spec in H.
  apply vec_cons_eq.
  destruct H. split. auto. auto.
Qed.

Lemma apl1_apl:
  forall A (n:nat),
  (apl n)^~1; apl n = id (t A (S n)).
Proof.
intros. 
rel_ext.
- unfold apl; unfold series; unfold converse; unfold id.
  intro. destruct H as [k H0 H1].
  destruct k. simpl in H0; simpl in H1.
  rewrite <- H0; rewrite <- H1.
  auto.
- unfold apl; unfold series; unfold converse; unfold id.
  intro. exists (hd x, tl x).
  simpl. symmetry. apply eta.
  simpl. symmetry. rewrite <- H. apply eta.
Qed. 

Lemma vec_shiftin_eq:
  forall A (n:nat) (a0 a1: A)(t0 t1: t A n),
  shiftin a0 t0 = shiftin a1 t1 <->
  a0 = a1 /\ t0 = t1.
Proof.
  split; [|now intros [-> ->]].
  induction t0 as [|n te t0' IH] in t1|-*.
  - pose proof (nil_spec t1) as ->. simpl.
    intros [=]. easy.
  - pose proof (eta t1) as ->. simpl.
    intros [-> [-> ->]%IH]%cons_inj.
    split; [easy|].
    now rewrite <-eta.
Qed.

Lemma vec_shiftin_eq' A n (t0 : t A n) :
  match n as n' return t A n' -> Prop with 0 => fun _ => True | S nn =>
      fun t0 => shiftin (last t0) (shiftout t0) = t0 end t0.
Proof.
  induction t0 as [|el1 n t0' IH]; [easy|].
  destruct t0' as [|el2 n t0']; [easy|].
  simpl in IH|-*. rewrite IH. easy.
Qed.

Lemma vec_shiftin_eq2 A n (t0 t1 : t A (S n)) :
    t0 = t1 <-> shiftin (last t0) (shiftout t0) = shiftin (last t1) (shiftout t1).
Proof. 
  now rewrite !(vec_shiftin_eq' A (S n)). 
Qed.

Lemma vec_shiftin_last_shiftout:
  forall A (n:nat) (x: t A (S n)),
  x = shiftin (last x) (shiftout x).
Proof.
  intros. symmetry. exact (vec_shiftin_eq' A (S n) x).
Qed.

Lemma apr_apr1:
  forall A (n:nat),
  apr n; (apr n)^~1 = id (t A n * A).
Proof.
intros.
rel_ext.
- unfold apr; unfold converse; unfold id; unfold series.
  intros. destruct H as [k H0 H1].
  destruct x as [t0 a0]; destruct x0 as [t1 a1].
  simpl in H0; simpl in H1.
  apply pair_equal_spec.
  assert (shiftin a0 t0 = shiftin a1 t1).
    rewrite H0. auto.
  apply and_comm. apply vec_shiftin_eq. auto.
- unfold apr; unfold converse; unfold id; unfold series.
  intros.
  destruct x as [t0 a0]; destruct x0 as [t1 a1].
  apply pair_equal_spec in H. destruct H.
  simpl.
  exists (shiftin a0 t0). auto.
  rewrite <- H0; rewrite <- H. auto.
Qed.

Lemma apr1_apr:
  forall A (n:nat),
  (apr n)^~1; apr n = id (t A (S n)).
Proof.
intros.
rel_ext.
- unfold apr; unfold converse; unfold id; unfold series.
  intros. destruct H as [k H0 H1].
  destruct k.
  simpl in H0; simpl in H1.
  rewrite <- H0. auto.
- unfold apr; unfold converse; unfold id; unfold series.
  intros. 
  exists (shiftout x, last x).
  all: simpl; subst x0.
  rewrite <- vec_shiftin_last_shiftout. reflexivity.
  rewrite <- vec_shiftin_last_shiftout. reflexivity.
Qed.
