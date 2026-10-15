(* Beside and below circuit definitions and characterisation lemmas. *)
Require Export wire.

(* ================================================================= *)
(*  Beside: structural and pointwise                                  *)
(* ================================================================= *)

Definition beside {A B C D E F G}
  (R: rel (A*B) (D*G)) (S: rel (G*C) (E*F)) :=
  rsh; FST R; lsh; SND S; rsh.

Definition beside_pw {A B C D E F G}
  (R: rel (A*B) (D*G)) (S: rel (G*C) (E*F)):
  rel (A*(B*C)) ((D*E)*F) :=
  fun '(a, (b, c)) '((d, e), f) =>
    exists2 g, R (a,b) (d,g) & S (g,c) (e,f).

Lemma beside_dual:
  forall A B C D E F G 
  (R: rel (A*B) (D*G)) (S: rel (G*C) (E*F)),
  beside R S = beside_pw R S.
Proof.
  intros.
  unfold beside, beside_pw.
  rel_ext; destruct x as [a [b c]]; destruct x0 as [[d e] f].
- intros [k [k0 [k1 [k2 [Ha [Hb Hc]] HFST] [H1 [H2 H3]]] HSND] [Hd [He Hf]]].
  destruct k2 as [[a1 b1] c1]. destruct k1 as [[d2 g2] c2].
  destruct k0 as [d3 [g3 c3]]. destruct k as [d4 [e4 f4]].
  simpl in *. subst.
  unfold FST, parallel, id in HFST; simpl in HFST.
  destruct HFST as [HR Hc]. subst c3.
  unfold SND, parallel, id in HSND; simpl in HSND.
  destruct HSND as [Hd HS]. subst d3.
  exists g3; assumption.
- intros [g HR HS].
  exists (d, (e, f)). exists (d, (g, c)). exists ((d, g), c). exists ((a, b), c).
  all: unfold rsh, lsh, FST, SND, parallel, id; simpl; auto.
Qed.

Notation " R <--> S " := (beside R S)
  (at level 39, left associativity) : function_scope.

(* ================================================================= *)
(*  Below: structural and pointwise                                   *)
(* ================================================================= *)

Definition below {A B C D E F G}
  (R: rel (A*G) (D*E)) (S: rel (B*C) (G*F)) :=
  lsh; SND S; rsh; FST R; lsh.
  
Definition below_pw {A B C D E F G}
  (R: rel (A*G) (D*E)) (S: rel (B*C) (G*F)) :=
  fun '((a, b), c) '(d, (e, f)) =>
    exists2 g, R (a,g) (d,e) & S (b,c) (g,f).
    
Lemma below_dual:
  forall A B C D E F G 
  (R: rel (A*G) (D*E)) (S: rel (B*C) (G*F)),
  below R S = below_pw R S.
Proof.
  intros.
  unfold below, below_pw.
  rel_ext; destruct x as [[a b] c]; destruct x0 as [d [e f]].
- intros [k [k0 [k1 [k2 [Ha [Hb Hc]] HSND] [H1 [H2 H3]]] HFST] [Hd [He Hf]]].
  destruct k2 as [a2 [b2 c2]]. destruct k1 as [a1 [g1 f1]].
  destruct k0 as [[a0 g0] f0]. destruct k as [[d1 e1] f1'].
  simpl in *. subst.
  unfold SND, parallel, id in HSND; simpl in HSND.
  destruct HSND as [<- HS].
  unfold FST, parallel, id in HFST; simpl in HFST.
  destruct HFST as [HR <-].
  exists g0; assumption.
- intros [g HR HS].
  exists ((d,e),f). exists ((a,g),f). exists (a,(g,f)). exists (a,(b,c)).
  all: unfold lsh, rsh, FST, SND, parallel, id; simpl; auto.
Qed.

Notation " R <||> S " := (below R S)
  (at level 39, left associativity) : function_scope.
