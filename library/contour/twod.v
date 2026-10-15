Require Export rec.

(* ================================================================= *)
(*  Beside: structural and pointwise                                  *)
(* ================================================================= *)

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
Proof.
  intros.
  unfold beside, beside_pw.
  rel_ext; destruct x as [a [b c]]; destruct x0 as [[d e] f].
- intros [k [k0 [k1 [k2 [Ha [Hb Hc]] HFST] [H1 [H2 H3]]] HSND] [Hd [He Hf]]].
  destruct k2 as [[a1 b1] c1]. destruct k1 as [[d2 g2] c2].
  destruct k0 as [d3 [g3 c3]]. destruct k as [d4 [e4 f4]].
  simpl in *. subst.
  unfold FST, parallel, id in HFST; simpl in HFST.
  destruct HFST as [HR Hc]. subst c3.
  unfold SND, parallel, id in HSND; simpl in HSND.
  destruct HSND as [Hd HS]. subst d3.
  exists g3; assumption.
- intros [g HR HS].
  exists (d, (e, f)). exists (d, (g, c)). exists ((d, g), c). exists ((a, b), c).
  all: unfold rsh, lsh, FST, SND, parallel, id; simpl; auto.
Qed.

Notation " R <--> S " := (beside R S)
  (at level 39, left associativity) : function_scope.

(* ================================================================= *)
(*  Below: structural and pointwise                                   *)
(* ================================================================= *)

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
Proof.
  intros.
  unfold below, below_pw.
  rel_ext; destruct x as [[a b] c]; destruct x0 as [d [e f]].
- intros [k [k0 [k1 [k2 [Ha [Hb Hc]] HSND] [H1 [H2 H3]]] HFST] [Hd [He Hf]]].
  destruct k2 as [a2 [b2 c2]]. destruct k1 as [a1 [g1 f1]].
  destruct k0 as [[a0 g0] f0]. destruct k as [[d1 e1] f1'].
  simpl in *. subst.
  unfold SND, parallel, id in HSND; simpl in HSND.
  destruct HSND as [<- HS].
  unfold FST, parallel, id in HFST; simpl in HFST.
  destruct HFST as [HR <-].
  exists g0; assumption.
- intros [g HR HS].
  exists ((d,e),f). exists ((a,g),f). exists (a,(g,f)). exists (a,(b,c)).
  all: unfold lsh, rsh, FST, SND, parallel, id; simpl; auto.
Qed.

Notation " R <||> S " := (below R S)
  (at level 39, left associativity) : function_scope.

(* ================================================================= *)
(*  Reusable Ltac                                                     *)
(* ================================================================= *)

(** Unfold all pointwise/structural definitions *)
Ltac unfold_pw :=
  unfold beside_pw, below_pw, FST, SND,
         parallel, id, series, converse, apl, apr.

(** Full setup for pointwise lemmas: rewrite to _pw, unfold, destruct *)
Ltac pw_setup :=
  rewrite ?beside_dual, ?below_dual;
  unfold beside_pw, below_pw, FST, SND, parallel, id, series;
  rel_ext;
  repeat match goal with
  | [ x : _ * _ |- _ ] => destruct x
  end;
  simpl.

(** Forward direction of _dual proofs (both apl and beside/below).
    After unfold_pw, the hypothesis has let-bound intermediates from
    beside_pw/below_pw.  Intro opaquely, destruct to reduce let, subst.
    For apr variants, also rewrites shiftout_shiftin/last_shiftin. *)
Ltac dual_fwd_apl :=
  intros [k [k0 [? ?] Hmid] [? ?]];
  (destruct k0 as [[? ?] ?] || destruct k0 as [? [? ?]]);
  simpl in Hmid;
  (destruct k as [? [? ?]] || destruct k as [[? ?] ?]);
  simpl in *;
  destruct Hmid as [g ? ?];
  subst;
  exists g; assumption.

(* ================================================================= *)
(*  Beside/Below composition laws                                     *)
(* ================================================================= *)

Lemma beside_comp:
  forall X (A B C D E F: rel X X)
  (R S: rel (X*X) (X*X)),
  [A,[B,C]]; (R <--> S); [[D,E],F] =
  ([A,B];R;FST D) <--> (SND C; S; [E,F]).
Proof.
  intros. pw_setup.
  - intros [m2 [m1 [HA [HB HC]] Hbeside] [[HD HE] HF]].
    destruct m1 as [a' [b' c']]. simpl in Hbeside.
    destruct m2 as [[d' e'] f']. destruct Hbeside as [g HR HS]. simpl in *.
    exists g.
    + exists (d', g). exists (a', b'). simpl; auto. exact HR.
      unfold parallel, id; simpl; auto.
    + exists (e', f'). exists (g, c').
      unfold parallel, id; simpl; auto. exact HS. simpl; auto.
  - intros [g [k1 [k2 [HA HB] HR] [HD Hg]] [k3 [k4 [Hg2 HC] HS] [HE HF]]].
    destruct k1 as [d' g1]. destruct k2 as [a' b'].
    destruct k3 as [e' f']. destruct k4 as [g2 c'].
    simpl in *. subst.
    exists ((d', e'), f'). exists (a', (b', c')).
    + simpl; auto.
    + simpl. exists g2; assumption.
    + simpl; auto.
Qed.

Lemma below_comp:
  forall X (A B C D E F: rel X X)
  (R S: rel (X*X) (X*X)),
  [[A,B],C]; (R <||> S); [D,[E,F]] =
  (FST A; R; [D,E]) <||> ([B,C]; S; SND F).
Proof.
  intros. pw_setup.
  - intros [m2 [m1 [[HA HB] HC] Hbelow] [HD [HE HF]]].
    destruct m1 as [[a' b'] c']. simpl in Hbelow.
    destruct m2 as [d' [e' f']]. destruct Hbelow as [g HR HS]. simpl in *.
    exists g.
    + exists (d', e'). exists (a', g).
      split; [exact HA | reflexivity]. exact HR. split; [exact HD | exact HE].
    + exists (g, f'). exists (b', c').
      split; [exact HB | exact HC]. exact HS. split; [reflexivity | exact HF].
  - intros [g [k1 [k2 [HA Hg] HR] [HD HE]] [k3 [k4 [HB HC] HS] [Hg2 HF]]].
    destruct k1 as [d' e']. destruct k2 as [a' g1].
    destruct k3 as [g2 f']. destruct k4 as [b' c'].
    simpl in *. subst.
    exists (d', (e', f')). exists ((a', b'), c').
    + simpl; auto.
    + simpl. exists g1; assumption.
    + simpl; auto.
Qed.

(* ================================================================= *)
(*  Associators as beside/below of identities                         *)
(* ================================================================= *)

Definition rsh2 {A B C} :=
  [id A, id B] <--> [id B, id C].

Lemma rsh_dual:
  forall A B C, rsh (A:=A) (B:=B) (C:=C) = rsh2.
Proof.
  intros. unfold rsh2. rewrite beside_dual.
  unfold beside_pw, rsh, parallel, id.
  rel_ext; destruct x as [a [b c]]; destruct x0 as [[d e] f]; simpl.
- intros [Ha [Hb Hc]]. exists b; auto.
- intros [g [Ha Hb] [Hc Hd]]. subst. auto.
Qed.

Definition lsh2 {A B C} :=
  [id A, id B] <||> [id B, id C].

Lemma lsh_dual:
  forall A B C, lsh (A:=A) (B:=B) (C:=C) = lsh2.
Proof.
  intros. unfold lsh2. rewrite below_dual.
  unfold below_pw, lsh, parallel, id.
  rel_ext; destruct x as [[a b] c]; destruct x0 as [d [e f]]; simpl.
- intros [Ha [Hb Hc]]. exists b; auto.
- intros [g [Ha Hb] [Hc Hd]]. subst. auto.
Qed.

(* ================================================================= *)
(*  Beside/Below wire-shuffling lemmas                                *)
(* ================================================================= *)

Lemma beside_fst:
  forall A B C D E F G H (R: rel (A*B) (C*D)) (S: rel (E*F) (G*H)) (T: rel D E),
  R <--> (FST T; S) = (R; SND T) <--> S.
Proof.
  intros. pw_setup.
  - intros [d HR [k [Te Hf] HS]].
    destruct k as [e f']. simpl in *. subst.
    exists e. exists (c, d). exact HR. simpl; auto. exact HS.
  - intros [e [k HR [Hc Te]] HS].
    destruct k as [c' d]. simpl in *. subst.
    exists d. exact HR. exists (e, f). simpl; auto. exact HS.
Qed.

Lemma beside_snd:
  forall A B C D E F G H (R: rel (A*B) (C*D)) (S: rel (D*E) (F*G)) (T: rel H E),
  R <--> (SND T; S) = SND (SND T); (R <--> S).
Proof.
  intros. pw_setup.
  - intros [d' HR [k [Hd Te] HS]].
    destruct k as [d'' e]. simpl in *. subst.
    exists (a, (b, e)). simpl; auto.
    simpl. exists d''; [exact HR | exact HS].
  - intros [k [Ha [Hb Te]] Hbeside].
    destruct k as [a' [b' e]]. simpl in *. subst.
    destruct Hbeside as [d' HR HS].
    exists d'. exact HR. exists (d', e). simpl; auto. exact HS.
Qed.

Lemma beside_block_para:
  forall A B C D E F G H I
  (R: rel (A*B) (C*D)) (S: rel (D*E) (F*G))
  (T: rel F H) (U: rel G I),
  R <--> (S; [T, U]) = (R <--> S); [SND T, U].
Proof.
  intros. pw_setup.
  - intros [d HR [k Hk [HT HU]]].
    destruct k as [f g]. simpl in *.
    exists ((c, f), g).
    + exists d; [exact HR | exact Hk].
    + simpl. split; [split; [reflexivity | exact HT] | exact HU].
  - intros [k Hbeside Hpara].
    destruct k as [[c' f] g]. simpl in *.
    destruct Hbeside as [d HR HS].
    destruct Hpara as [[Hc HT] HU]. subst.
    exists d. exact HR. exists (f, g). exact HS. simpl; auto.
Qed.

(* ================================================================= *)
(*  Row: definitions                                                  *)
(* ================================================================= *)

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

(* ================================================================= *)
(*  Row: duality proofs                                               *)
(* ================================================================= *)

Lemma row_dual:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row n R = row_pw n R.
Proof.
  intros. induction n; [reflexivity|].
  simpl. rewrite IHn, beside_dual. unfold_pw.
  rel_ext; destruct x as [a v]; destruct x0 as [w a_out]; simpl.
  + dual_fwd_apl.
  + intros [g HR Hrow].
    exists ((hd w, tl w), a_out). exists (a, (hd v, tl v)).
    * split; [reflexivity | simpl; symmetry; apply eta].
    * simpl. exists g; assumption.
    * simpl. split; [symmetry; apply eta | reflexivity].
Qed.

(** Forward direction of apr-based _dual proofs.
    Same as dual_fwd_apl but with shiftin rewrites. *)
Ltac dual_fwd_apr :=
  intros [k [k0 [? ?] Hmid] [? ?]];
  (destruct k0 as [[? ?] ?] || destruct k0 as [? [? ?]]);
  simpl in Hmid;
  (destruct k as [? [? ?]] || destruct k as [[? ?] ?]);
  simpl in *;
  destruct Hmid as [g ? ?];
  subst;
  rewrite ?shiftout_shiftin, ?last_shiftin;
  exists g; assumption.

Lemma row2_dual2:
  forall A B C (n:nat) (R: rel (A*B) (C*A)),
  row2 n R = row_pw2 n R.
Proof.
  intros. induction n; [reflexivity|].
  simpl. rewrite IHn, beside_dual. unfold_pw.
  rel_ext; destruct x as [a v]; destruct x0 as [w a_out]; simpl.
  + dual_fwd_apr.
  + intros [g Hrow HR].
    exists ((shiftout w, last w), a_out). exists (a, (shiftout v, last v)).
    * split; [reflexivity | simpl; symmetry; apply vec_shiftin_last_shiftout].
    * simpl. exists g; assumption.
    * simpl. split; [symmetry; apply vec_shiftin_last_shiftout | reflexivity].
Qed.

Lemma row_pw_snoc:
  forall A B C (n:nat) (R: rel (A*B) (C*A))
  (a a_out: A) (v: t B n) (b: B) (w: t C n) (c: C),
  row_pw (S n) R (a, shiftin b v) (shiftin c w, a_out) <->
  exists2 g, row_pw n R (a, v) (w, g) & R (g, b) (c, a_out).
Proof.
  intros A B C n. induction n; intros.
  - rewrite (nil_spec v), (nil_spec w). simpl. split.
    + intros [g HR Hz]. unfold row_zero in Hz. simpl in Hz. subst.
      exists a. unfold row_zero; simpl; reflexivity. exact HR.
    + intros [g Hz HR]. unfold row_zero in Hz. simpl in Hz. subst.
      exists a_out. exact HR. unfold row_zero; simpl; reflexivity.
  - rewrite (eta v), (eta w). simpl shiftin.
    simpl row_pw at 1. fold (@row_pw A B C).
    split.
    + intros [g1 HR1 Hrest].
      apply IHn in Hrest. destruct Hrest as [g2 Hrow HR2].
      exists g2; [simpl; exists g1; assumption | exact HR2].
    + intros [g2 Hrow HR2].
      simpl in Hrow. destruct Hrow as [g1 HR1 Hrow'].
      exists g1. exact HR1. apply IHn. exists g2; assumption.
Qed.

