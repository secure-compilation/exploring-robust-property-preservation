From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Require Import DiffEvents.
Require Import DiffTraceModel.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.

Definition prop {k : level} := @trace k -> Prop.

Notation "π1 ⊆ π2" := (forall t, π1 t -> π2 t) (at level 50).

Definition Safety {k : level} (π : @prop k) : Prop :=
  forall t, ~ π t ->
       (exists m, prefix m t /\
            (forall t', prefix m t' -> ~ π t')).

(* CA: for now this is axiomatized but we can recover it by modifying
       results from TraceTopology.v *)
Axiom Cl: forall {k: level}, @prop k -> @prop k.
Axiom Cl_bigger: forall {k: level} (π: @prop k), π ⊆ (Cl π). 
Axiom Cl_Safety: forall {k: level} π, Safety (@Cl k π).

Definition hprop {k : level} := @prop k -> Prop.

Definition SSC {k: level} (H: @hprop k)  : Prop :=
  forall h, H h ->
       (forall b : prop, b ⊆ h -> H b).


Definition sCl {k : level} (H : @hprop k) : @hprop k :=
  fun b => exists b', H b' /\ b ⊆ b'.

Lemma sCl_bigger {k : level} (H : @hprop k) : H ⊆ (sCl H). 
Proof. firstorder. Qed.   
  
Lemma sCl_SCH {k : level} (H : @hprop k) : SSC (sCl H).
Proof.
  move => h [b' [Hb' bb']] b b_h. exists b'; auto.
Qed.

