Require Export rec loop.
Require Import preHorners_prerequisite.

Lemma Horners:
  forall A B (n:nat) (P:rel A A) (Q:rel B B) (R:rel (A*B) B),
  [P,Q]; R = R; Q ->
  [tri n P, pow n Q]; (rdr n R) = rdr n (SND Q; R).
Proof.
(* Open obligation; no solution supplied. *)
