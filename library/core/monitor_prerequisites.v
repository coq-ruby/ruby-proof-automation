Require Export rec.
Require Import Arith Lia Eqdep_dec.
Local Open Scope nat_scope.

(* ================================================================ *)
(*  Relational avionics monitor circuits.                           *)
(*  Checked relational circuit prerequisites.                       *)
(* ================================================================ *)

(* ---------- arithmetic ---------- *)
Lemma S2nM1 : forall n:nat, 2^n = S (2^n - 1).
Proof. intro n. assert (1 <= 2^n). { induction n; simpl; lia. } lia. Qed.

Lemma Sn2 : forall n:nat, 2 ^ S n = 2^n + 2^n.
Proof. intro n. simpl. lia. Qed.

Lemma pow2_pos : forall n, 1 <= 2 ^ n.
Proof. induction n; simpl; lia. Qed.

(* ---------- relational cast ---------- *)
Definition cast_rel {A} {m n:nat} (H: m = n) : rel (t A m) (t A n) :=
  fun u v => eq_rect m (t A) u n H = v.

Lemma cast_rel_refl : forall A n (H: n = n), cast_rel (A:=A) H = id (t A n).
Proof.
  intros A n H.
  assert (H = eq_refl) by apply Eqdep_dec.UIP_refl_nat.
  subst H. unfold cast_rel, id. simpl. reflexivity.
Qed.

Lemma cast_rel_chain :
  forall A m n p (H1: m = n) (H2: n = p),
  cast_rel (A:=A) H1 ; cast_rel H2 = cast_rel (eq_trans H1 H2).
Proof.
  intros A m n p H1 H2. destruct H1. destruct H2. simpl.
  rewrite !cast_rel_refl. apply id_left.
Qed.

Lemma cast_rel_iso :
  forall A m n (H: m = n),
  cast_rel (A:=A) H ; cast_rel (eq_sym H) = id (t A m).
Proof.
  intros A m n H. destruct H. rewrite !cast_rel_refl. apply id_left.
Qed.

Lemma cast_rel_iso2 :
  forall A m n (H: m = n),
  cast_rel (A:=A) (eq_sym H) ; cast_rel H = id (t A n).
Proof.
  intros A m n H. destruct H. rewrite !cast_rel_refl. apply id_left.
Qed.

(* casts commute with any index-parametric block *)
Lemma cast_tri :
  forall A m n (H: m = n) (X: rel A A),
  tri m X ; cast_rel H = cast_rel H ; tri n X.
Proof. intros A m n H X. destruct H. rewrite cast_rel_refl.
  rewrite id_left. rewrite id_right. reflexivity. Qed.

(* ---------- circuit combinators ---------- *)
Definition mfork {A} (n:nat) : rel A (t A n) :=
  fun a v => v = const a n.

Definition apn {A} (p q:nat) : rel (t A p * t A q) (t A (p+q)) :=
  fun u w => append (fst u) (snd u) = w.

Lemma mapn_zero_id :
  forall A, [ @mapn_zero A A , id A ] = id (t A 0 * A).
Proof.
  intro A. unfold parallel, mapn_zero, id. rel_ext.
  - destruct x as [u a], x0 as [v b]. simpl.
    intros [[Hu Hv] Hab]. subst. reflexivity.
  - destruct x as [u a], x0 as [v b]. simpl.
    intro H. inversion H; subst.
    repeat split; try reflexivity; apply empty_is_nil.
Qed.

Lemma tri_one :
  forall A (X: rel A A), tri 1 X = id (t A 1).
Proof.
  intros A X. simpl. rewrite mapn_zero_id.
  rewrite id_right. apply apr1_apr.
Qed.

(* cons/snoc wiring: shiftin over cons is definitional *)
Lemma apl_apr_interchange :
  forall A (p:nat),
  FST (apl p) ; apr (S p) = lsh ; SND (@apr A p) ; apl (S p).
Proof.
  intros A p.
  unfold FST, SND, parallel, apl, apr, lsh, series, id. rel_ext.
  - destruct x as [[a u] b].
    intros [[w b'] [Hw Hb] Hs]. simpl in Hw, Hb, Hs.
    subst b'. subst w. subst x0.
    exists (a, shiftin b u).
    + exists (a, (u, b)).
      * repeat split.
      * split; reflexivity.
    + simpl. reflexivity.
  - destruct x as [[a u] b].
    intros [k [j [Hj1 [Hj2 Hj3]] [Hk1 Hk2]] Ha].
    destruct j as [ja [ju jb]], k as [ka kv]. simpl in *.
    subst a u b ka kv.
    exists ((ja :: ju)%vector, jb).
    + split; reflexivity.
    + simpl. exact Ha.
Qed.

Lemma rdl_zero_fst :
  forall A (X: rel A A),
  [X, @mapn_zero A A] ; rdl_zero = rdl_zero ; X.
Proof.
  intros A X. unfold parallel, mapn_zero, rdl_zero, series. rel_ext.
  - destruct x as [a u]. simpl.
    intros [[a' v] [Hx [Hu Hv]] Hf]. simpl in *. subst. 
    exists a. reflexivity. exact Hx.
  - destruct x as [a u]. simpl.
    intros [a' Ha Hx]. subst.
    exists (x0, nil A); simpl.
    + split. exact Hx. split. apply empty_is_nil. reflexivity.
    + reflexivity.
Qed.

Lemma shiftin_const :
  forall A (a:A) (q:nat), shiftin a (const a q) = const a (S q).
Proof.
  intros A a q. induction q; simpl.
  - reflexivity.
  - rewrite IHq. reflexivity.
Qed.

Lemma mfork_snoc :
  forall A (q:nat), @mfork A (S q) = fork ; [ mfork q , id A ] ; apr q.
Proof.
  intros A q. unfold mfork, fork, parallel, id, apr, series. rel_ext.
  - intro H. subst x0.
    exists (const x q, x).
    + exists (x, x). split; reflexivity. split; reflexivity.
    + simpl. apply shiftin_const.
  - intros [[u b] [[c d] [Hc Hd] [Hu Hb]] Hs]. simpl in *. subst.
    exact (shiftin_const A b q).
Qed.

Lemma cast_mfork :
  forall A m n (H: m = n), @mfork A m ; cast_rel H = mfork n.
Proof.
  intros A m n H. destruct H. rewrite cast_rel_refl. apply id_right.
Qed.

Lemma hd_shiftin :
  forall B (m:nat) (b:B) (u: t B (S m)), hd (shiftin b u) = hd u.
Proof. intros B m b u. apply (caseS' u). intros h tl. reflexivity. Qed.

Lemma tl_shiftin :
  forall B (m:nat) (b:B) (u: t B (S m)), tl (shiftin b u) = shiftin b (tl u).
Proof. intros B m b u. apply (caseS' u). intros h tl. reflexivity. Qed.

Lemma cons_hd_tl :
  forall B (m:nat) (v: t B (S m)), hd v :: tl v = v.
Proof. intros B m v. apply (caseS' v). intros h tl. reflexivity. Qed.

Lemma fst_snd_comm :
  forall A B C E (X: rel A B) (Y: rel C E),
  FST X ; SND Y = SND Y ; FST X.
Proof.
  intros. unfold FST, SND.
  rewrite <- !para_series. rewrite !id_left. rewrite !id_right. reflexivity.
Qed.

Lemma snd_conv :
  forall A B C (X: rel A B), ((@SND A B C X)^~1) = SND (X^~1).
Proof.
  intros. unfold SND. rewrite para_conv. rewrite id_conv. reflexivity.
Qed.

Lemma rdl_S :
  forall A B (m:nat) (Q: rel (A*B) A),
  rdl (S m) Q = (SND (apl m))^~1 ; rsh ; FST Q ; rdl m Q.
Proof. reflexivity. Qed.

Lemma rdl_snoc :
  forall A B (m:nat) (Q: rel (A*B) A),
  rdl (S m) Q = SND ((apr m)^~1) ; rsh ; FST (rdl m Q) ; Q.
Proof.
  intros A B m. induction m; intro Q.
  - (* m = 0 *)
    rewrite rdl_S. rewrite snd_conv. simpl (rdl 0 Q).
    unfold SND, FST, parallel, apl, apr, converse, rsh, rdl_zero, id, series.
    rel_ext.
    + destruct x as [a v].
      intros [k3 [k2 [k1 Hs1 Hrsh] HFQ] Hz].
      destruct k1 as [a1 [w0 u1]]; destruct k2 as [[a2 w2] u2]; destruct k3 as [r1 u3].
      simpl in *.
      destruct Hs1 as [Ea Hcons].
      destruct Hrsh as [E1 [E2 E3]].
      destruct HFQ as [HQ Eu].
      exists (a, w0).
      { exists ((a, nil B), w0).
        { exists (a, (nil B, w0)).
          { split. reflexivity. simpl.
            rewrite (@empty_is_nil B u1) in Hcons. exact Hcons. }
          { repeat split. } }
        { split; reflexivity. } }
      rewrite Ea, E1, E2. rewrite <- Hz. exact HQ.
    + destruct x as [a v].
      intros [k3 [k2 [k1 Hs1 Hrsh] HFr] HQ].
      destruct k1 as [a1 [U1 b1]]; destruct k2 as [[a2 U2] b2]; destruct k3 as [f b3].
      simpl in *.
      destruct Hs1 as [Ea Hsh].
      destruct Hrsh as [E1 [E2 E3]].
      destruct HFr as [Hf Eb].
      rewrite (@empty_is_nil B U1) in Hsh. simpl in Hsh.
      exists (x0, nil B).
      { exists ((a, b1), nil B).
        { exists (a, (b1, nil B)).
          { split. reflexivity. simpl. exact Hsh. }
          { repeat split. } }
        { split. rewrite Ea, E1, Hf, E3, Eb. exact HQ. reflexivity. } }
      reflexivity.
  - (* S m *)
    rewrite rdl_S at 1.
    rewrite IHm at 1.
    rewrite rdl_S.
    rewrite !snd_conv.
    rewrite <- !fst_series.
    norm_left.
    unfold SND, FST, parallel, apl, apr, converse, rsh, id, series.
    rel_ext.
    + destruct x as [a v].
      intros [k6 [k5 [k4 [k3 [k2 [k1 H1 H2] H3] H4] H5] H6] H7].
      destruct k1 as [a1 [w0 u]]; destruct k2 as [[a2 w2] u2];
      destruct k3 as [r1 u3]; destruct k4 as [r4 [u4 b4]];
      destruct k5 as [[r5 u5] b5]; destruct k6 as [f b6].
      simpl in *.
      destruct H1 as [Ea1 Hcons].
      destruct H2 as [Ea2 [Ew2 Eu2]].
      destruct H3 as [HQ1 Eu3].
      destruct H4 as [Er4 Hsh4].
      destruct H5 as [Er5 [Eu5 Eb5]].
      destruct H6 as [Hfold Eb6].
      rewrite <- Eu3, <- Eu2 in Hsh4.
      exists (f, b4).
      { exists ((r1, u4), b4).
        { exists (((a, w0), u4), b4).
          { exists ((a, (w0, u4)), b4).
            { exists ((a, (w0 :: u4)%vector), b4).
              { exists (a, ((w0 :: u4)%vector, b4)).
                { split. reflexivity. simpl.
                  rewrite Hsh4. exact Hcons. }
                { repeat split. } }
              { repeat split. } }
            { repeat split. } }
          { repeat split; try reflexivity.
            rewrite Ea1, Ea2, Ew2. exact HQ1. } }
        { repeat split; try reflexivity.
          rewrite Er4, Er5, Eu5. exact Hfold. } }
      rewrite Eb5, Eb6. exact H7.
    + destruct x as [a v].
      intros [k6 [k5 [k4 [k3 [k2 [k1 H1 H2] H3] H4] H5] H6] H7].
      destruct k1 as [a1 [U1 bb1]]; destruct k2 as [[a2 U2] bb2];
      destruct k3 as [[a3 [w3 t3]] bb3]; destruct k4 as [[[a4 w4] t4] bb4];
      destruct k5 as [[r5 t5] bb5]; destruct k6 as [f bb6].
      simpl in *.
      destruct H1 as [Ea1 Hsh].
      destruct H2 as [Ea2 [EU2 Eb2]].
      destruct H3 as [[Ea3 Hc3] Eb3].
      destruct H4 as [[Ea4 [Ew4 Et4]] Eb4].
      destruct H5 as [[HQ Et5] Eb5].
      destruct H6 as [Hfold Eb6].
      rewrite <- EU2 in Hc3.
      rewrite <- Hc3 in Hsh. simpl in Hsh.
      exists (f, bb1).
      { exists ((r5, t3), bb1).
        { exists (r5, (t3, bb1)).
          { exists (r5, shiftin bb1 t3).
            { exists ((a, w3), shiftin bb1 t3).
              { exists (a, (w3, shiftin bb1 t3)).
                { split. reflexivity. simpl. exact Hsh. }
                { repeat split. } }
              { repeat split; try reflexivity.
                rewrite Ea1, Ea2, Ea3, Ea4, Ew4. exact HQ. } }
            { repeat split; try reflexivity. } }
          { repeat split. } }
        { repeat split; try reflexivity.
          rewrite Et4, Et5. exact Hfold. } }
      rewrite Eb2, Eb3, Eb4, Eb5, Eb6. exact H7.
Qed.
Lemma tri_S :
  forall A (n:nat) (X: rel A A),
  tri (S n) X = (apr n)^~1 ; [tri n X, X^^n] ; apr n.
Proof. reflexivity. Qed.

Lemma shiftin_inj :
  forall B (m:nat) (a b: B) (u w: t B m),
  shiftin a u = shiftin b w -> a = b /\ u = w.
Proof.
  intros B m. induction m; intros a b u w H.
  - rewrite (@empty_is_nil B u), (@empty_is_nil B w) in *.
    simpl in H. apply (f_equal (@hd B 0)) in H. simpl in H.
    split. exact H. reflexivity.
  - revert H. apply (caseS' u). intros h u'. apply (caseS' w). intros h' w'.
    simpl. intro H.
    assert (Hh : h = h') by (apply (f_equal (@hd B (S m))) in H; exact H).
    assert (Ht : shiftin a u' = shiftin b w')
      by (apply (f_equal (@tl B (S m))) in H; exact H).
    destruct (IHm a b u' w' Ht) as [E1 E2].
    subst. split; reflexivity.
Qed.

Lemma W2 :
  forall A (m:nat),
  @apr A (S m) ; (apl (S m))^~1 ; SND ((apr m)^~1) =
  FST ((apl m)^~1) ; lsh.
Proof.
  intros A m.
  unfold FST, SND, parallel, apl, apr, converse, lsh, id, series. rel_ext.
  - destruct x as [v c]; destruct x0 as [h0 [p0 q0]].
    intros [[h2 t2] [k1 Hs Hc2] [Eh Hsr]].
    simpl in *. subst k1.
    apply (f_equal (@hd A (S m))) in Hc2 as Hh2.
    apply (f_equal (@tl A (S m))) in Hc2 as Ht2.
    simpl in Hh2, Ht2. rewrite hd_shiftin in Hh2. rewrite tl_shiftin in Ht2.
    rewrite Ht2 in Hsr.
    destruct (shiftin_inj _ _ _ _ _ _ Hsr) as [Ec Ep].
    exists ((h0, p0), q0).
    + split. simpl. rewrite <- Eh, Hh2, Ep. apply cons_hd_tl.
      simpl. symmetry. exact Ec.
    + repeat split.
  - destruct x as [v c]; destruct x0 as [h0 [p0 q0]].
    intros [[[h1 p1] q1] [Hapl Ec] [E1 [E2 E3]]].
    simpl in *. subst v q1 h1 p1 q0.
    exists (h0, shiftin c p0).
    + exists (shiftin c ((h0 :: p0)%vector)).
      * reflexivity.
      * reflexivity.
    + repeat split.
Qed.

Lemma fork_assoc :
  forall A, @fork A ; FST fork = fork ; SND fork ; rsh.
Proof.
  intro A. unfold fork, FST, SND, parallel, rsh, id, series. rel_ext.
  - destruct x0 as [[b c] d].
    intros [[e g] [He1 He2] [[Hb1 Hb2] Hd]]. simpl in *.
    subst e g b c d.
    exists (x, (x, x)).
    + exists (x, x).
      * split; reflexivity.
      * split. reflexivity. split; reflexivity.
    + repeat split.
  - destruct x0 as [[b c] d].
    intros [[e [g h]] [[e1 g1] [E1 E2] [E3 [G1 G2]]] [F1 [F2 F3]]].
    simpl in *.
    subst e1 g1 e g h b c d.
    exists (x, x).
    + split; reflexivity.
    + split. split; reflexivity. reflexivity.
Qed.

Lemma rsh_para :
  forall A B C E F G (X: rel A B) (Y: rel C E) (Z: rel F G),
  [X, [Y, Z]] ; rsh = rsh ; [[X, Y], Z].
Proof.
  intros. unfold parallel, rsh, series. rel_ext.
  - destruct x as [a [c f]]; destruct x0 as [[b e] g].
    intros [[b' [e' g']] [Hx [Hy Hz]] [E1 [E2 E3]]]. simpl in *. subst.
    exists ((a, c), f).
    + repeat split.
    + repeat split; assumption.
  - destruct x as [a [c f]]; destruct x0 as [[b e] g].
    intros [[[a' c'] f'] [E1 [E2 E3]] [[Hx Hy] Hz]]. simpl in *. subst.
    exists (b, (e, g)).
    + repeat split; assumption.
    + repeat split.
Qed.

Lemma fst_snd_para :
  forall A B C E (Cx: rel A B) (Z: rel C E),
  FST Cx ; SND Z = [Cx, Z].
Proof.
  intros. unfold FST, SND.
  rewrite <- para_series. rewrite id_left. rewrite id_right. reflexivity.
Qed.

(* ---------- determinism ---------- *)
Definition det {X Y : Type} (T: rel X Y) : Prop :=
  forall x y z, T x y -> T x z -> y = z.

Lemma det_series :
  forall X Y Z (S: rel X Y) (T: rel Y Z),
  det S -> det T -> det (S ; T).
Proof.
  intros X Y Z S T HS HT x y z [v Hv Hv'] [w Hw Hw'].
  assert (E : v = w) by (eapply HS; eauto). subst w.
  eapply HT; eauto.
Qed.

Lemma det_para :
  forall X Y Z W (S: rel X Y) (T: rel Z W),
  det S -> det T -> det ([S, T]).
Proof.
  intros X Y Z W S T HS HT [x1 x2] [y1 y2] [z1 z2] [H1 H2] [H3 H4].
  simpl in *. f_equal; [eapply HS | eapply HT]; eauto.
Qed.

Lemma det_id : forall X, det (id X).
Proof. intros X x y z Hy Hz. unfold id in *. subst y z. reflexivity. Qed.

Lemma det_mfork : forall X n, det (@mfork X n).
Proof. intros X n x y z Hy Hz. unfold mfork in *. subst y z. reflexivity. Qed.

Lemma det_rsh : forall X Y Z, det (@rsh X Y Z).
Proof.
  intros X Y Z [a [b c]] [[d e] f] [[g h] i] [E1 [E2 E3]] [F1 [F2 F3]].
  simpl in *. subst. reflexivity.
Qed.

Lemma det_apr : forall X n, det (@apr X n).
Proof.
  intros X n [u a] y z Hy Hz. unfold apr in *. simpl in *. subst y z. reflexivity.
Qed.

Lemma det_apr1 : forall X n, det ((@apr X n)^~1).
Proof.
  intros X n u [pv pa] [qv qa] Hp Hq. unfold converse, apr in *. simpl in *.
  rewrite <- Hq in Hp.
  destruct (shiftin_inj _ _ _ _ _ _ Hp) as [E1 E2]. subst. reflexivity.
Qed.

Lemma det_apl1 : forall X n, det ((@apl X n)^~1).
Proof.
  intros X n v [ph pt] [qh qt] Hp Hq. unfold converse, apl in *. simpl in *.
  rewrite <- Hq in Hp.
  assert (Eh : ph = qh) by (apply (f_equal (@hd X n)) in Hp; exact Hp).
  assert (Et : pt = qt) by (apply (f_equal (@tl X n)) in Hp; exact Hp).
  subst. reflexivity.
Qed.

Lemma det_pow : forall X (T: rel X X) c, det T -> det (T ^^ c).
Proof.
  intros X T c HT. induction c; simpl.
  - apply det_id.
  - apply det_series; assumption.
Qed.

Lemma det_absorb :
  forall X Y (T: rel X Y), det T -> T ; fork = fork ; [T, T].
Proof.
  intros X Y T HT. unfold series, fork, parallel. rel_ext.
  - destruct x0 as [b c].
    intros [v Hv [E1 E2]]. subst b c.
    exists (x, x).
    + split; reflexivity.
    + simpl. split; exact Hv.
  - destruct x0 as [b c].
    intros [[p q] [E1 E2] [H1 H2]]. simpl in *. subst p q.
    assert (E : b = c) by (eapply HT; eauto). subst c.
    exists b. exact H1. split; reflexivity.
Qed.

(* ---------- the designs ---------- *)
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
Proof.
  unfold mfork, apl, converse, rdl_zero, id, series. rel_ext.
  - intros [pr [u Hu Ha] Hr]. subst u.
    apply (f_equal (@hd A 0)) in Ha. simpl in Ha.
    rewrite Ha in Hr. exact Hr.
  - intro H. subst x0.
    exists (x, nil A).
    + exists (const x 1). reflexivity. reflexivity.
    + reflexivity.
Qed.



Lemma Hpush_pow :
  forall c, [D^^c, D^^c] ; R = R ; D^^c.
Proof.
  induction c.
  - simpl. rewrite para_id. rewrite id_left. rewrite id_right. reflexivity.
  - simpl. rewrite para_series.
    rewrite <- (series_assoc _ _ _ _ ([D^^c, D^^c]) ([D, D]) R).
    rewrite Hpush.
    rewrite (series_assoc _ _ _ _ ([D^^c, D^^c]) R D).
    rewrite IHc.
    rewrite series_assoc. reflexivity.
Qed.

(* cast-free form of P over structural sizes *)
Definition PP (m:nat) : rel A A :=
  mfork (S m) ; tri (S m) D ; (apl m)^~1 ; rdl m R.

Lemma PP0 : PP 0 = id A.
Proof.
  unfold PP. rewrite tri_one. rewrite id_right. apply base_wire.
Qed.

Lemma P_as_PP : forall n, P n = PP (2^n - 1).
Proof.
  intro n. unfold P, PP.
  rewrite <- (series_assoc _ _ _ _ (mfork (2^n)) (tri (2^n) D) (cast_rel (S2nM1 n))).
  rewrite cast_tri.
  rewrite (series_assoc _ _ _ _ (mfork (2^n)) (cast_rel (S2nM1 n)) (tri (S (2^n - 1)) D)).
  rewrite cast_mfork. reflexivity.
Qed.







Lemma Ddet : det D.
Proof.
  intros x y z Hy Hz.
  assert (H : (D^~1 ; D) y z) by (exists x; assumption).
  rewrite D_c2 in H. exact H.
Qed.

Lemma det_tri : forall k, det (tri k D).
Proof.
  induction k.
  - intros x y z [_ Hy] [_ Hz]. rewrite Hy, Hz. reflexivity.
  - simpl. repeat apply det_series.
    + apply det_apr1.
    + apply det_para; [exact IHk | apply det_pow; exact Ddet].
    + apply det_apr.
Qed.

Lemma det_rdl : forall k, det (rdl k R).
Proof.
  induction k.
  - intros x y z Hy Hz. simpl in Hy, Hz. unfold rdl_zero in *.
    rewrite <- Hy, <- Hz. reflexivity.
  - rewrite rdl_S. repeat apply det_series.
    + rewrite snd_conv. apply det_para; [apply det_id | apply det_apl1].
    + apply det_rsh.
    + apply det_para; [exact Rdet | apply det_id].
    + exact IHk.
Qed.

Lemma det_PP : forall m, det (PP m).
Proof.
  intro m. unfold PP.
  apply det_series; [apply det_series; [apply det_series; [apply det_mfork | apply det_tri] | apply det_apl1] | apply det_rdl].
Qed.



End Monitor.