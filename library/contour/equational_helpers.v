Require Export contour_prerequisites.

(* Generic algebra: no contour theorem or cell-specific hypothesis. *)
Lemma parallel_power:
  forall A B (P : rel A A) (Q : rel B B) n,
  [P,Q]^^n = [P^^n,Q^^n].
Proof.
  intros A B P Q n. induction n.
  - cbn [pow]. symmetry. apply para_id.
  - cbn [pow]. rewrite IHn, <- para_series. reflexivity.
Qed.

Lemma power_cancellation:
  forall A (P Q : rel A A), P;Q = id A ->
  forall n, P^^n;Q^^n = id A.
Proof.
  intros A P Q H n. induction n.
  - cbn [pow]. apply id_left.
  - rewrite <- (pow_left A n Q).
    change ((P^^n;P);(Q;Q^^n) = id A).
    series_rewrite_lhs H. rewrite id_right. exact IHn.
Qed.

Lemma inverse_power_extend:
  forall A (P Q : rel A A), P;Q = id A ->
  forall n, Q^^n = P;Q^^(S n).
Proof.
  intros A P Q H n. rewrite <- (pow_left A n Q).
  series_rewrite_rhs H. rewrite id_left. reflexivity.
Qed.

Lemma conjugation_power:
  forall A B (L : rel A A) (M : rel B B) (P : rel A B),
  P = L;P;M -> forall n, P = L^^n;P;M^^n.
Proof.
  intros A B L M P H n. induction n.
  - cbn [pow]. rewrite id_left, id_right. reflexivity.
  - transitivity (L;P;M); [exact H|].
    rewrite IHn at 1. norm_left.
    series_rewrite_lhs (pow_left A n L).
    cbn [pow]. series_reflexivity.
Qed.

Lemma triangle_converse:
  forall A (P : rel A A) n,
  (tri n P)^~1 = tri n (P^~1).
Proof.
  intros A P n. induction n.
  - change ((mapn 0 P)^~1 = mapn 0 (P^~1)).
    apply mapn_conv.
  - cbn [tri]. rewrite !series_conv, para_conv, conv_conv, IHn, pow_conv.
    series_reflexivity.
Qed.

(* The append form of an arbitrary uniform row, independent of contours. *)
Lemma row_append:
  forall A B C (P : rel (A*B) (C*A)) n,
  row (S n) P =
  SND ((apr n)^~1); (row n P <--> P); FST (apr n).
Proof.
  intros A B C P n. rewrite !row_dual, beside_dual.
  unfold SND, FST, parallel, series, converse, apr, id.
  rel_ext; destruct x as [a v]; destruct x0 as [w z]; simpl.
  - rewrite (vec_shiftin_last_shiftout B n v),
            (vec_shiftin_last_shiftout C n w).
    intro H. apply row_pw_snoc in H. destruct H as [g Hp Hq].
    exists ((shiftout w, last w), z).
    + exists (a, (shiftout v, last v)).
      * split; [reflexivity|reflexivity].
      * exists g; assumption.
    + split; reflexivity.
  - intros [out [input [Ha Hv] Hbeside] [Hw Hz]].
    destruct input as [a' [v' b]], out as [[w' c] z']; simpl in *.
    subst a' v w z'. destruct Hbeside as [g Hp Hq].
    apply row_pw_snoc. exists g; assumption.
Qed.

(* Arbitrary endorelations on six external ports and the internal seam.
   This is ordinary beside exchange, with no cancellation assumption. *)
Lemma beside_boundary_exchange:
  forall A B C D E
  (P : rel (A*B) (C*A)) (Q : rel (A*D) (E*A))
  (U : rel B B) (V : rel C C) (H K N : rel A A)
  (L : rel D D) (M : rel E E),
  (SND U;P;[V,H]) <--> ([K,L];Q;[M,N]) =
  SND ([U,L]); (P <--> (FST (H;K);Q)); [[V,M],N].
Proof.
  intros A B C D E P Q U V H K N L M.
  rewrite !beside_dual.
  unfold beside_pw, FST, SND, parallel, series, id.
  rel_ext; destruct x as [a [b d]]; destruct x0 as [[c e] z]; simpl.
  - intros [g [pout [pin [Ha HU] HP] [HV HH]]
              [qout [qin [HK HL] HQ] [HM HN]]].
    destruct pin as [a0 b0], pout as [c0 h0],
             qin as [k0 d0], qout as [e0 n0]; simpl in *.
    subst a0.
    exists ((c0,e0),n0).
    + exists (a,(b0,d0)).
      * split; [reflexivity|split; assumption].
      * exists h0; [exact HP|].
        exists (k0,d0); [|exact HQ].
        split; [exists g; assumption|reflexivity].
    + split; [split; assumption|exact HN].
  - intros [out [input [Ha [HU HL]] Hbeside] [[HV HM] HN]].
    destruct input as [a0 [b0 d0]], out as [[c0 e0] n0]; simpl in *.
    subst a0. destruct Hbeside as [h0 HP [qin [HHK Hd] HQ]].
    destruct qin as [k0 d1]; simpl in *. subst d1.
    destruct HHK as [g HH HK]. exists g.
    + exists (c0,h0). exists (a,b0).
      * split; [reflexivity|exact HU].
      * exact HP.
      * split; assumption.
    + exists (e0,n0). exists (k0,d0).
      * split; assumption.
      * exact HQ.
      * split; assumption.
Qed.

(* Moving a factor on the final port of any beside composition. *)
Lemma beside_final_factor:
  forall A B C D E F G H
  (P : rel (A*B) (C*D)) (Q : rel (D*E) (F*G)) (U : rel G H),
  (P <--> Q); SND U = P <--> (Q;SND U).
Proof.
  intros. symmetry. unfold SND at 1. rewrite beside_block_para.
  unfold SND. rewrite para_id. reflexivity.
Qed.

(* Generic boundary collection through invertible interface wires. *)
Lemma interface_input:
  forall A X Y (W : rel X Y) (P : rel X X),
  W;W^~1 = id X ->
  SND (C:=A) (W^~1); SND P = SND (W^~1;P;W); SND (W^~1).
Proof.
  intros A X Y W P H. rewrite !snd_series.
  f_equal. norm_left. series_rewrite_rhs H.
  rewrite id_right. reflexivity.
Qed.

Lemma interface_output:
  forall X Y A B (W : rel X Y) (P : rel X X) (Q : rel A B),
  W;W^~1 = id X ->
  [P,Q];FST W = FST W;[W^~1;P;W,Q].
Proof.
  intros X Y A B W P Q H.
  rewrite para_fst, fst_para.
  f_equal. norm_left. series_rewrite_rhs H.
  rewrite id_left. reflexivity.
Qed.

