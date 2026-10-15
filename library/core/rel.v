Require Export axioms.

Definition rel (A B: Type) := A -> B -> Prop.

Definition series {A B C} 
  (R: rel A B) (S: rel B C):
  rel A C :=
  fun i j => exists2 k, R i k & S k j.

Notation " Q ; R " := (series Q R)
  (at level 40, left associativity).
  
Definition parallel {A B X Y}
  (R: rel A X) (S: rel B Y):
  rel (A*B) (X*Y) :=
  fun i j => R (fst i) (fst j) /\ S (snd i) (snd j).

Notation " [ Q , R ] " := (parallel Q R)
  (at level 38, left associativity).
  
Lemma series_assoc:
  forall A B C D (R:rel A B) (S:rel B C) (T:rel C D),
  R;(S;T) = (R;S);T.
Proof.
  intros.
  unfold series.
  apply functional_extensionality. intro.
  apply functional_extensionality. intro.
  apply propositional_extensionality. split.
  - intros [c ? [d ? ?]]. eauto.
  - intros [c [d ? ?] ?]. eauto.
Qed.

(* ================================================================= *)
(*  Congruence lemmas                                                 *)
(* ================================================================= *)

Lemma series_congr_left:
  forall A B C (R R': rel A B) (S: rel B C),
  R = R' -> R;S = R';S.
Proof. intros. subst. reflexivity. Qed.

Lemma series_congr_right:
  forall A B C (R: rel A B) (S S': rel B C),
  S = S' -> R;S = R;S'.
Proof. intros. subst. reflexivity. Qed.

(* ================================================================= *)
(*  Normalization                                                     *)
(* ================================================================= *)

Ltac norm_left :=
  repeat rewrite series_assoc.

Ltac norm_right :=
  repeat rewrite <- series_assoc.
  
Ltac series_reflexivity :=
  norm_left; reflexivity.

(* ================================================================= *)
(*  Core: bracket and rewrite at current position                     *)
(* ================================================================= *)

(** Try to rewrite [lem] at the current head of the chain.
    Applies [series_assoc] 0..4 times to group elements leftward,
    then rewrites. Closes with [norm_left; reflexivity]. *)

Ltac bracket_rewrite_here lem :=
  (rewrite lem; norm_left; reflexivity) +
  (rewrite series_assoc; rewrite lem; norm_left; reflexivity) +
  (do 2 rewrite series_assoc; rewrite lem; norm_left; reflexivity) +
  (do 3 rewrite series_assoc; rewrite lem; norm_left; reflexivity) +
  (do 4 rewrite series_assoc; rewrite lem; norm_left; reflexivity) +
  (do 5 rewrite series_assoc; rewrite lem; norm_left; reflexivity) +
  (do 6 rewrite series_assoc; rewrite lem; norm_left; reflexivity) +
  (do 7 rewrite series_assoc; rewrite lem; norm_left; reflexivity) +
  (do 8 rewrite series_assoc; rewrite lem; norm_left; reflexivity).

Ltac bracket_rewrite_here_rev lem :=
  (rewrite <- lem; norm_left; reflexivity) +
  (rewrite series_assoc; rewrite <- lem; norm_left; reflexivity) +
  (do 2 rewrite series_assoc; rewrite <- lem; norm_left; reflexivity) +
  (do 3 rewrite series_assoc; rewrite <- lem; norm_left; reflexivity) +
  (do 4 rewrite series_assoc; rewrite <- lem; norm_left; reflexivity) +
  (do 5 rewrite series_assoc; rewrite <- lem; norm_left; reflexivity) +
  (do 6 rewrite series_assoc; rewrite <- lem; norm_left; reflexivity) +
  (do 7 rewrite series_assoc; rewrite <- lem; norm_left; reflexivity) +
  (do 8 rewrite series_assoc; rewrite <- lem; norm_left; reflexivity).

(** Non-closing variants for [series_rewrite] (no reflexivity). *)

Ltac bracket_and_rewrite lem :=
  (rewrite lem; norm_left) +
  (rewrite series_assoc; rewrite lem; norm_left) +
  (do 2 rewrite series_assoc; rewrite lem; norm_left) +
  (do 3 rewrite series_assoc; rewrite lem; norm_left) +
  (do 4 rewrite series_assoc; rewrite lem; norm_left) +
  (do 5 rewrite series_assoc; rewrite lem; norm_left) +
  (do 6 rewrite series_assoc; rewrite lem; norm_left) +
  (do 7 rewrite series_assoc; rewrite lem; norm_left) +
  (do 8 rewrite series_assoc; rewrite lem; norm_left).

Ltac bracket_and_rewrite_rev lem :=
  (rewrite <- lem; norm_left) +
  (rewrite series_assoc; rewrite <- lem; norm_left) +
  (do 2 rewrite series_assoc; rewrite <- lem; norm_left) +
  (do 3 rewrite series_assoc; rewrite <- lem; norm_left) +
  (do 4 rewrite series_assoc; rewrite <- lem; norm_left) +
  (do 5 rewrite series_assoc; rewrite <- lem; norm_left) +
  (do 6 rewrite series_assoc; rewrite <- lem; norm_left) +
  (do 7 rewrite series_assoc; rewrite <- lem; norm_left) +
  (do 8 rewrite series_assoc; rewrite <- lem; norm_left).

(* ================================================================= *)
(*  Recursive descent for single-side rewriting                       *)
(* ================================================================= *)

(** [descend_and_rewrite lem] works on a goal of the form
        CHAIN = ?evar
    (concrete on the left, evar on the right, after [symmetry]).

    It tries to rewrite [lem] at the current position. If that fails,
    it uses [apply series_congr_right] to descend one level into the
    right subtree and recurses.

    Why this works with evars:
    - [apply series_congr_right] on [R;S = ?X] unifies [?X] with
      [R;?X'] and produces subgoal [S = ?X']. The evar gets
      partially instantiated, which is fine.
    - [rewrite series_assoc] on [A;(B;C) = ?X] rewrites the concrete
      LHS; the evar on the RHS is carried along untouched.
    - [reflexivity] at the end unifies the evar with whatever the
      LHS has become.

    Termination: the LHS strictly shrinks at each descent. When it
    is no longer a series node, [series_congr_right] fails and the
    recursion stops. *)

Ltac descend_and_rewrite lem :=
  bracket_rewrite_here lem +
  (apply series_congr_right; descend_and_rewrite lem).

Ltac descend_and_rewrite_rev lem :=
  bracket_rewrite_here_rev lem +
  (apply series_congr_right; descend_and_rewrite_rev lem).

(* ================================================================= *)
(*  series_rewrite_peel: both sides share a common prefix                  *)
(* ================================================================= *)

Ltac peel_series_prefix :=
  (apply series_congr_right; peel_series_prefix) + idtac.

Ltac series_rewrite_peel lem :=
  norm_right; 
  peel_series_prefix; 
  bracket_and_rewrite lem.
  
Ltac series_rewrite_peel_rev lem :=
  norm_right; 
  peel_series_prefix; 
  bracket_and_rewrite_rev lem.

(* ================================================================= *)
(*  series_rewrite_lhs / _rhs: single-side rewriting                  *)
(* ================================================================= *)

(** [series_rewrite_lhs lem]: rewrite [lem] on the LHS only.

    Given goal [LHS = RHS]:
    1. Capture [LHS] via [match goal].
    2. [assert (H : _ = LHS)]: creates subgoal [?Z = LHS].
    3. In the [by] clause:
       a. [symmetry]: goal becomes [LHS = ?Z] (concrete left, evar right).
       b. [norm_right]: right-normalise the concrete LHS.
       c. [descend_and_rewrite lem]: recursively descend the chain
          using [series_congr_right] until the rewrite target is at
          the head, then bracket and rewrite.
    4. Back in the main goal, [rewrite <- H] replaces the original
       LHS with the rewritten form. *)

Ltac series_rewrite_lhs lem :=
  let H := fresh "Hsrl" in
  norm_left;
  match goal with
  | |- ?LHS = _ =>
    assert (H : _ = LHS) by
      (symmetry; norm_right; descend_and_rewrite lem);
    rewrite <- H; clear H;
    norm_left
  end.

Ltac series_rewrite_lhs_rev lem :=
  let H := fresh "Hsrl" in
  norm_left;
  match goal with
  | |- ?LHS = _ =>
    assert (H : _ = LHS) by
      (symmetry; norm_right; descend_and_rewrite_rev lem);
    rewrite <- H; clear H;
    norm_left
  end.

Ltac series_rewrite_rhs lem :=
  let H := fresh "Hsrr" in
  norm_left;
  match goal with
  | |- _ = ?RHS =>
    assert (H : _ = RHS) by
      (symmetry; norm_right; descend_and_rewrite lem);
    rewrite <- H; clear H;
    norm_left
  end.

Ltac series_rewrite_rhs_rev lem :=
  let H := fresh "Hsrr" in
  norm_left;
  match goal with
  | |- _ = ?RHS =>
    assert (H : _ = RHS) by
      (symmetry; norm_right; descend_and_rewrite_rev lem);
    rewrite <- H; clear H;
    norm_left
  end.

Ltac series_rewrite lem :=
  series_rewrite_peel lem +
  series_rewrite_lhs lem +
  series_rewrite_rhs lem.

Ltac series_rewrite_rev lem :=
  series_rewrite_peel_rev lem +
  series_rewrite_lhs_rev lem +
  series_rewrite_rhs_rev lem.

