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
Require Import HSafetyPreservation.
Require Import SafetyCriterion.

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section HSafeCriterion.
  
  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable T_evs S_evs : Events.
  Variable T_end S_end : Endstates.

  Local Definition trace__S := @trace S_evs S_end.
  Local Definition finpref__S := @finpref S_evs S_end.
  Local Definition trace__T := @trace T_evs T_end.
  Local Definition finpref__T := @finpref T_evs T_end.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.
  Local Definition hprop__S := hprop trace__S.
  Local Definition hprop__T := hprop trace__T.

  Local Definition HSafety__S := @HSafe S_evs S_end.
  Local Definition HSafety__T := @HSafe T_evs T_end.


  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition beh__T := beh Target_Semantics.
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target.
  Local Definition hsat__S := hsat Source_Semantics.
  Local Definition hsat__T := hsat Target_Semantics.

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).

  Variable rel : trace__S -> trace__T -> Prop.

  Local Definition adjunction :=  induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.

  Lemma τ_mono : monotone τ'.
  Proof. move/Galois_equiv: rel_adjunction_law. by move => [H1 H2]. Qed.

  Definition rel_SC : Prop := rel_SC  compilation_chain
                                   Source_Semantics Target_Semantics
                                   rel.

  Local Definition sCl_σ : hprop__T -> hprop__S := sCl_σ σ'.
  Local Definition hsCl_τ : hprop__S -> hprop__T := hsCl_τ τ'.

  Local Definition hsCl_τhP := hsCl_τhP compilation_chain
                                       Source_Semantics Target_Semantics
                                       τ'.


  Local Definition sCl_σhP := sCl_σhP compilation_chain
                                      Source_Semantics Target_Semantics
                                      σ'.

  Local Definition  hsCl_τ_SCHP_sClσHSafeP := hsCl_τ_SCHP_sClσHSafeP
                                              compilation_chain
                                              Source_Semantics Target_Semantics
                                              rel_adjunction_law. 
  
  Theorem rel_SC_hsClτSCHP : rel_SC <-> (forall (P : prg__S) (H__S : hprop__S), SSC H__S -> hsCl_τhP P H__S).
  Admitted. 

  Theorem rel_TC_sCl_σRSCHP : rel_SC <-> (forall (W : prg__S) (H__T : hprop__T), HSafe H__T ->  sCl_σhP W H__T).
  Proof.
   by rewrite hsCl_τ_SCHP_sClσHSafeP rel_SC_hsClτSCHP.
  Qed.

End HSafeCriterion.
