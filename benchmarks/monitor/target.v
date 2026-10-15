Require Import monitor_prerequisites.
Require Import Arith Lia.
Section Task.
Local Open Scope nat_scope.
Variable A : Type.
Variable D : rel A A.
Variable R : rel (A*A) A.
Hypothesis D_c2 : D^~1 ; D = id A.
Hypothesis Hpush : [D,D] ; R = R ; D.
Hypothesis Hassoc : rsh ; FST R ; R = SND R ; R.
Hypothesis Rdet : det R.
Local Notation P := (P A D R).
Local Notation Q := (Q A D R).
Local Notation PP := (PP A D R).


Lemma monitor : forall n, P n = Q n.
Proof.
(* Open obligation; no solution supplied. *)
