From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

(* Some preliminary lemmas and definition on subset inclusion *)
Notation "π1 ⊆ π2" := (forall t, π1 t -> π2 t) (at level 50).

Lemma subset_trans {X : Type} (π1 π2 π3 : X -> Prop) :
  π1 ⊆ π2 -> π2 ⊆ π3 -> π1 ⊆ π3.
Proof.
  move => H1 H2 x π1_x. apply: H2. by apply: H1.
Qed.

Lemma subset_ref {X : Type} (π : X -> Prop) :
  π ⊆ π.
Proof. by move => t. Qed.

Lemma mutual_inclusion {X : Type} (π1 π2 : X -> Prop) :
  π1 ⊆ π2 -> π2 ⊆ π1 -> π1 = π2.
Proof.
  move => H1 H2.
  apply: functional_extensionality => x.
  apply: prop_extensionality. split; [by apply: H1 | by apply: H2].
Qed.

Notation "f ∘ g" := (fun x => f ( g x )) (at level 50).

Definition single {X : Type} (t : X) : X -> Prop := fun x => x = t.

Definition prod_map {X Y : Type} (f : (X -> Prop) -> (Y -> Prop)) : ((X -> Prop) * (X -> Prop)) ->
                                                              ((Y -> Prop) * (Y -> Prop)) :=
  fun x =>
    (f (fst x), f (snd x)).
