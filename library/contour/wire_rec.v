Require Export wire Vector.
Export VectorNotations.

Definition apl {A} (n:nat):
  rel (A * t A n) (t A (S n)) :=
  fun i j => fst i :: snd i = j.

Definition apr {A} (n:nat):
  rel (t A n * A) (t A (S n)) :=
  fun i j => shiftin (snd i) (fst i) = j.


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

Lemma shiftout_shiftin: forall A n (a: A) (v: t A n),
  shiftout (shiftin a v) = v.
Proof.
  intros. induction v; simpl; [reflexivity | rewrite IHv; reflexivity].
Qed.

Lemma last_shiftin: forall A n (a: A) (v: t A n),
  last (shiftin a v) = a.
Proof.
  intros. induction v; simpl; [reflexivity | rewrite IHv; reflexivity].
Qed.

Lemma hd_shiftin: forall A n (a: A) (v: t A (S n)),
  hd (shiftin a v) = hd v.
Proof. intros. rewrite (eta v). simpl. reflexivity. Qed.

Lemma tl_shiftin: forall A n (a: A) (v: t A (S n)),
  tl (shiftin a v) = shiftin a (tl v).
Proof. intros. rewrite (eta v). simpl. reflexivity. Qed.

