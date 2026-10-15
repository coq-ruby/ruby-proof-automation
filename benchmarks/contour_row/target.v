Require Import equational_helpers.


Lemma contour_row:
  forall (A B : Type) (EA : rel A A) (EB : rel B B) (n : nat) (R : rel (A * B) (B * A)),
  EA; EA^~1 = id A ->
  EA^~1; EA = id A ->
  R = R \\ [EB^~1, EA^~1] ->
  row n R = SND (tri n EB); row n (R; SND EA); [(tri n EB)^~1, (EA^~1)^^n].
Proof.
(* Open obligation; no solution supplied. *)
