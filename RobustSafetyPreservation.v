From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Setoid.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.
Require Import RobustTraceProperty.
Require Import UcoRobustPreservation.

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section RobustSafetyPreservation.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable T_evs S_evs : Events.
  Variable T_end S_end : Endstates.

  Local Definition trace__S := @trace S_evs S_end.
  Local Definition finpref__S := @finpref S_evs S_end.
  Local Definition trace__T := @trace T_evs T_end.
  Local Definition finpref__T := @finpref T_evs T_end.

  Local Definition prop__S := prop trace__S.
  Local Definition Safety__S := @Safety S_evs S_end.
  Local Definition prop__T := prop trace__T.
  Local Definition Safety__T := @Safety T_evs T_end.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition sat__S := sat Source_Semantics.
  Local Definition sat__T := sat Target_Semantics.

  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  Variable σ : prop__T -> prop__S.
  Variable τ : prop__S -> prop__T.

  Local Definition σRP := σRP compilation_chain
                              Source_Semantics Target_Semantics
                              σ.

  Definition Cl_τRP := τRP compilation_chain
                           Source_Semantics Target_Semantics
                           (Cl ∘ τ).

  Theorem σSafetyP_Cl_τTP :
    (Adjunction_law τ σ) ->
    ( (forall P (π__T : prop__T), Safety π__T -> σRP P π__T) <->
      (forall P (π__S : prop__S), Cl_τRP P π__S)).
  Proof.
    move => H_adj.
    setoid_rewrite <- (@uco_adjuncts _ _ _ _ _ _ _ σ τ safety_uco).
    rewrite -Safety_Cl_prop.
    reflexivity.
    assumption.
  Qed.

End RobustSafetyPreservation.
