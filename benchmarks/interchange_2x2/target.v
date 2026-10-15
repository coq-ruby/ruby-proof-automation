Require Import grid_components.

Lemma interchange_2x2:
  forall A B (R: rel (A*B) (B*A)),
  (R <--> R) <||> (R <--> R) = (R <||> R) <--> (R <||> R).
Proof.
(* Open obligation; no solution supplied. *)
