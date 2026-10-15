Require Export contour_prerequisites.

Lemma mapn_pw_total : forall A (E:rel A A),
 (forall a, exists b, E a b) -> forall n (v:t A n), exists w, mapn_pw n E v w.
Proof.
 intros A E H n. induction n; intros v.
 - exists (nil A). simpl. split; [apply empty_is_nil | reflexivity].
 - destruct (H (hd v)) as [b Hb]. destruct (IHn (tl v)) as [w Hw].
   exists (b :: w). simpl. auto.
Qed.

Lemma cell_transport : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA^~1; EA = id A -> EB^~1; EB = id B ->
 R = [EA,EB]; R; [EB^~1,EA^~1] ->
 forall a b c d a1 b1 c1 d1,
 EA a a1 -> EB b b1 -> EB c c1 -> EA d d1 ->
 (R (a,b) (c,d) <-> R (a1,b1) (c1,d1)).
Proof.
 intros A B EA EB R HA HB HR a b c d a1 b1 c1 d1 Ha Hb Hc Hd.
 split.
 - intro H. rewrite HR in H.
   destruct H as [[cm dm] [[am bm] [Ham Hbm] Hmid] [Hcm Hdm]].
   simpl in *. unfold converse in Hcm,Hdm.
   assert (am=a1) by (eapply cancel_func; eauto).
   assert (bm=b1) by (eapply cancel_func; eauto).
   assert (cm=c1) by (eapply cancel_func; eauto).
   assert (dm=d1) by (eapply cancel_func; eauto).
   subst. exact Hmid.
 - intro H. rewrite HR. exists (c1,d1).
   + exists (a1,b1); [split; assumption | exact H].
   + split; assumption.
Qed.

Lemma col_transport : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA; EA^~1 = id A -> EA^~1; EA = id A ->
 EB; EB^~1 = id B -> EB^~1; EB = id B ->
 R = [EA,EB]; R; [EB^~1,EA^~1] ->
 forall n (va va1 vb vb1:t A n) b b1 c c1,
 mapn_pw n EA va va1 -> mapn_pw n EA vb vb1 -> EB b b1 -> EB c c1 ->
 (col_pw n R (va,b) (c,vb) <-> col_pw n R (va1,b1) (c1,vb1)).
Proof.
 intros A B EA EB R HA1 HA2 HB1 HB2 HR n.
 induction n; intros va va1 vb vb1 b b1 c c1 Hva Hvb Hb Hc.
 - simpl. unfold col_zero. simpl. split; intro H.
   + subst c. eapply cancel_func; eauto.
   + subst c1. eapply cancel_inj; eauto.
 - simpl in Hva,Hvb. destruct Hva as [Hah Hat]. destruct Hvb as [Hvh Hvt].
   simpl. split.
   + intros [g Hcell Hrest].
     destruct (cancel_total B EB HB1 g) as [g1 Hg].
     exists g1.
     * apply (proj1 (cell_transport A B EA EB R HA2 HB2 HR _ _ _ _ _ _ _ _ Hah Hg Hc Hvh)). exact Hcell.
     * apply (proj1 (IHn _ _ _ _ _ _ _ _ Hat Hvt Hb Hg)). exact Hrest.
   + intros [g1 Hcell Hrest].
     destruct (cancel_surj B EB HB2 g1) as [g Hg].
     exists g.
     * apply (proj2 (cell_transport A B EA EB R HA2 HB2 HR _ _ _ _ _ _ _ _ Hah Hg Hc Hvh)). exact Hcell.
     * apply (proj2 (IHn _ _ _ _ _ _ _ _ Hat Hvt Hb Hg)). exact Hrest.
Qed.

Lemma col_conjugation : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA; EA^~1 = id A -> EA^~1; EA = id A ->
 EB; EB^~1 = id B -> EB^~1; EB = id B ->
 R = [EA,EB]; R; [EB^~1,EA^~1] -> forall n,
 col n R = [mapn n EA,EB]; col n R; [EB^~1,(mapn n EA)^~1].
Proof.
 intros A B EA EB R HA1 HA2 HB1 HB2 HR n.
 rewrite !col_dual, !mapn_dual.
 rel_ext; destruct x as [va b]; destruct x0 as [c vb].
 - intro H.
   destruct (mapn_pw_total A EA (cancel_total A EA HA1) n va) as [va1 Hva].
   destruct (mapn_pw_total A EA (cancel_total A EA HA1) n vb) as [vb1 Hvb].
   destruct (cancel_total B EB HB1 b) as [b1 Hb].
   destruct (cancel_total B EB HB1 c) as [c1 Hc].
   exists (c1,vb1).
   + exists (va1,b1).
     * split; assumption.
     * apply (proj1 (col_transport A B EA EB R HA1 HA2 HB1 HB2 HR n _ _ _ _ _ _ _ _ Hva Hvb Hb Hc)). exact H.
   + split; assumption.
 - intros [[c1 vb1] [[va1 b1] [Hva Hb] Hcol] [Hc Hvb]].
   apply (proj2 (col_transport A B EA EB R HA1 HA2 HB1 HB2 HR n _ _ _ _ _ _ _ _ Hva Hvb Hb Hc)). exact Hcol.
Qed.

Lemma mapn_power : forall A (E:rel A A) n m,
 (mapn n E)^^m = mapn n (E^^m).
Proof.
 intros A E n m. induction m.
 - simpl. symmetry. apply mapn_id.
 - simpl. rewrite IHm. rewrite <- mapn_series. reflexivity.
Qed.

Lemma mapn_cancellation : forall A (E:rel A A),
 E;E^~1 = id A -> forall n,
 mapn n E; (mapn n E)^~1 = id (t A n).
Proof.
 intros A E H n. rewrite mapn_conv, <- mapn_series, H. apply mapn_id.
Qed.
