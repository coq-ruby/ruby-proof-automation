Require Export grid_helpers equational_helpers.

(* Uniform conjugation and grid boundary transformations. *)
Lemma row_uniform_transport : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA;EA^~1=id A -> EA^~1;EA=id A ->
 EB;EB^~1=id B -> EB^~1;EB=id B ->
 R=[EA,EB];R;[EB^~1,EA^~1] ->
 forall m a a1 c c1 (v v1 w w1:t B m),
 EA a a1 -> EA c c1 -> mapn_pw m EB v v1 -> mapn_pw m EB w w1 ->
 (row_pw m R (a,v) (w,c) <-> row_pw m R (a1,v1) (w1,c1)).
Proof.
 intros A B EA EB R HA1 HA2 HB1 HB2 HR m.
 induction m; intros a a1 c c1 v v1 w w1 Ha Hc Hv Hw.
 - cbn [row_pw]. unfold row_zero. simpl. split; intro H.
   + subst c. eapply cancel_func; eauto.
   + subst c1. eapply cancel_inj; eauto.
 - cbn [mapn_pw] in Hv,Hw. destruct Hv as [Hvh Hvt], Hw as [Hwh Hwt].
   cbn [row_pw]. split.
   + intros [g Hcell Hrest].
     destruct (cancel_total A EA HA1 g) as [g1 Hg]. exists g1.
     * apply (proj1 (cell_transport A B EA EB R HA2 HB2 HR
         _ _ _ _ _ _ _ _ Ha Hvh Hwh Hg)). exact Hcell.
     * apply (proj1 (IHm _ _ _ _ _ _ _ _ Hg Hc Hvt Hwt)). exact Hrest.
   + intros [g1 Hcell Hrest].
     destruct (cancel_surj A EA HA2 g1) as [g Hg]. exists g.
     * apply (proj2 (cell_transport A B EA EB R HA2 HB2 HR
         _ _ _ _ _ _ _ _ Ha Hvh Hwh Hg)). exact Hcell.
     * apply (proj2 (IHm _ _ _ _ _ _ _ _ Hg Hc Hvt Hwt)). exact Hrest.
Qed.

Lemma row_uniform_conjugation : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA;EA^~1=id A -> EA^~1;EA=id A ->
 EB;EB^~1=id B -> EB^~1;EB=id B ->
 R=[EA,EB];R;[EB^~1,EA^~1] -> forall m,
 row m R = [EA,mapn m EB];row m R;[(mapn m EB)^~1,EA^~1].
Proof.
 intros A B EA EB R HA1 HA2 HB1 HB2 HR m.
 rewrite !row_dual, !mapn_dual.
 rel_ext; destruct x as [a v]; destruct x0 as [w c].
 - intro H.
   destruct (cancel_total A EA HA1 a) as [a1 Ha].
   destruct (cancel_total A EA HA1 c) as [c1 Hc].
   destruct (mapn_pw_total B EB (cancel_total B EB HB1) m v) as [v1 Hv].
   destruct (mapn_pw_total B EB (cancel_total B EB HB1) m w) as [w1 Hw].
   exists (w1,c1).
   + exists (a1,v1); [split; assumption|].
     apply (proj1 (row_uniform_transport A B EA EB R HA1 HA2 HB1 HB2 HR
       _ _ _ _ _ _ _ _ _ Ha Hc Hv Hw)). exact H.
   + split; assumption.
 - intros [[w1 c1] [[a1 v1] [Ha Hv] Hrow] [Hw Hc]].
   apply (proj2 (row_uniform_transport A B EA EB R HA1 HA2 HB1 HB2 HR
     _ _ _ _ _ _ _ _ _ Ha Hc Hv Hw)). exact Hrow.
Qed.

Lemma grid_conjugation : forall A B (EA:rel A A) (EB:rel B B)
 (R:rel (A*B) (B*A)),
 EA;EA^~1=id A -> EA^~1;EA=id A ->
 EB;EB^~1=id B -> EB^~1;EB=id B ->
 R=[EA,EB];R;[EB^~1,EA^~1] -> forall m n,
 grid m n R = [mapn n EA,mapn m EB];grid m n R;
 [(mapn m EB)^~1,(mapn n EA)^~1].
Proof.
 intros A B EA EB R HA1 HA2 HB1 HB2 HR m n. unfold grid.
 apply row_uniform_conjugation.
 - apply mapn_cancellation. exact HA1.
 - rewrite mapn_conv, <- mapn_series, HA2. apply mapn_id.
 - exact HB1.
 - exact HB2.
 - exact (col_conjugation A B EA EB R HA1 HA2 HB1 HB2 HR n).
Qed.

(* An arbitrary map followed by a triangle, at the append boundary. *)
Lemma map_triangle_snoc : forall A (E:rel A A) m b c (v w:t A m),
 (mapn (S m) E;tri (S m) E) (shiftin b v) (shiftin c w) <->
 (mapn m E;tri m E) v w /\ (E^^(S m)) b c.
Proof.
 intros A E m b c v w. split.
 - intros [u Hmap Htri]. destruct (snoc_inv A m u) as [d [z ->]].
   rewrite mapn_dual in Hmap.
   rewrite (mapn_pw_snoc A A m E b d v z) in Hmap.
   destruct Hmap as [Hbd Hmz]. rewrite <- (mapn_dual A A m E) in Hmz.
   apply tri_snoc in Htri. destruct Htri as [Htz Hdc].
   split; [exists z; assumption|].
   rewrite <- pow_left. exists d; assumption.
 - intros [[z Hmz Htz] Hpow]. rewrite <- pow_left in Hpow.
   destruct Hpow as [d Hbd Hdc]. exists (shiftin d z).
   + rewrite mapn_dual. rewrite (mapn_pw_snoc A A m E b d v z).
     split; [exact Hbd|].
     rewrite <- mapn_dual. exact Hmz.
   + apply tri_snoc. split; assumption.
Qed.

Lemma triangle_cons : forall A (E:rel A A) m b c (v w:t A m),
 tri (S m) E (b::v) (c::w) <->
 b=c /\ (mapn m E;tri m E) v w.
Proof.
 intros A E m. induction m; intros b c v w.
 - rewrite (nil_spec v), (nil_spec w).
   change (tri 1 E (shiftin b (nil A)) (shiftin c (nil A)) <->
     b=c /\ (mapn 0 E;tri 0 E) (nil A) (nil A)).
   rewrite tri_snoc. cbn [tri pow mapn]. unfold id, mapn_zero.
   split.
   + intros [_ H]. split; [exact H|]. exists (nil A); split; reflexivity.
   + intros [H _]. split; [split; reflexivity|exact H].
 - destruct (snoc_inv A m v) as [d [v0 ->]].
   destruct (snoc_inv A m w) as [e [w0 ->]].
   change (tri (S (S m)) E (shiftin d (b::v0)) (shiftin e (c::w0)) <->
     b=c /\ (mapn (S m) E;tri (S m) E) (shiftin d v0) (shiftin e w0)).
   rewrite tri_snoc, IHm, map_triangle_snoc. tauto.
Qed.

Lemma triangle_prepend : forall A (E:rel A A) m,
 tri (S m) E = (apl m)^~1;SND (mapn m E;tri m E);apl m.
Proof.
 intros A E m. rel_ext.
 - rewrite (eta x), (eta x0). intro H. apply triangle_cons in H.
   destruct H as [Hbc Hrest].
   exists (hd x0,tl x0).
   + exists (hd x,tl x).
     * unfold converse,apl; simpl; reflexivity.
     * split; assumption.
   + unfold apl; simpl; reflexivity.
 - intros [[c w] [[b v] Hin [Hbc Hrest]] Hout].
   unfold converse,apl in Hin,Hout. simpl in Hin,Hout. subst x x0.
   apply triangle_cons. split; assumption.
Qed.

Lemma triangle_prepend_right : forall A (E:rel A A) m,
 tri (S m) E = (apl m)^~1;SND (tri m E;mapn m E);apl m.
Proof.
 intros. rewrite triangle_prepend, tri_mapn. reflexivity.
Qed.

Lemma grid_step : forall A B (R:rel (A*B) (B*A)) m n,
 grid (S m) n R = SND ((apl m)^~1);
 (col n R <--> grid m n R);FST (apl m).
Proof. reflexivity. Qed.
