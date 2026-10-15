Require Export rec loop.

Lemma preHorners:
  forall A B (n:nat) (P: rel A A) (Q:rel B B) (R:rel (A*B) B),
  [P, Q]; R = R; Q ->
  [P ^^ n, Q ^^ n]; R = R; (Q ^^ n).
Proof.
(* Open obligation; no solution supplied. *)
