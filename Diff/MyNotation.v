From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import FunctionalExtensionality.
Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

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

Lemma mutual_inclusion {X : Set} (π1 π2 : X -> Prop) :
  π1 ⊆ π2 -> π2 ⊆ π1 -> π1 = π2.
Proof.
  move => H1 H2.
  apply: functional_extensionality => x.
  apply: prop_extensionality. split; [by apply: H1 | by apply: H2]. 
Qed.     

Notation "f ∘ g" := (fun x => f ( g x )) (at level 50).

