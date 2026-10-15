Require Import grid_support.


Lemma contour_right:
 forall (A B:Type) (EA:rel A A) (EB:rel B B) (m n:nat)
 (R:rel (A*B) (B*A)),
 EA; EA^~1 = id A -> EA^~1; EA = id A ->
 EB; EB^~1 = id B -> EB^~1; EB = id B ->
 R = R \\ [EB^~1, EA^~1] ->
 grid m n R = SND (tri m EB); grid m n (R; SND EA);
 [(tri m EB)^~1, mapn n ((EA^~1)^^m)].
Proof.
(* Open obligation; no solution supplied. *)
