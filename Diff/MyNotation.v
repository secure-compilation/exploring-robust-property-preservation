From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Some preliminary lemmas and definition on subset inclusion *)
Notation "π1 ⊆ π2" := (forall t, π1 t -> π2 t) (at level 50).

Lemma subset_trans {X : Set} (π1 π2 π3 : X -> Prop) :
  π1 ⊆ π2 -> π2 ⊆ π3 -> π1 ⊆ π3.
Proof.
  move => H1 H2 x π1_x. apply: H2. by apply: H1.  
Qed.

Lemma subset_ref {X : Set} (π : X -> Prop) :
  π ⊆ π.
Proof. by move => t. Qed. 