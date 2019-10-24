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
Require Import Def.
Require Import TraceCriterion.

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section Relation.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable trace__S trace__T : Set.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__T := beh Target_Semantics.
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition sat__S := sat Source_Semantics.
  Local Definition sat__T := sat Target_Semantics.

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).

  (* Cheating relation *)
  Definition rel : trace__S -> trace__T -> Prop :=
    fun t__S t__T => exists W, sem__S W t__S /\ sem__T (W ↓) t__T.

  Local Definition adjunction := induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition τTP := τTP compilation_chain
                              Source_Semantics Target_Semantics
                              τ'.


  Local Definition σTP := σTP compilation_chain
                              Source_Semantics Target_Semantics
                              σ'.


  Local Definition rel_TC := rel_TC compilation_chain
                                    Source_Semantics Target_Semantics
                                    rel.



  Theorem cmp_is_rel_TC : rel_TC.
  Proof.
    move => W t__T W_t.
    destruct (non_empty_sem Source_Semantics W) as [s W_s].
    exists s. split; auto. now exists W.
  Qed.

  Corollary cmp_is_τTP: τTP.
  Proof. setoid_rewrite <- rel_TC_τTP. exact cmp_is_rel_TC. Qed.

  Corollary cmp_is_σTP : σTP.
  Proof. setoid_rewrite <- rel_TC_σTP. exact cmp_is_rel_TC. Qed.


End Relation.
