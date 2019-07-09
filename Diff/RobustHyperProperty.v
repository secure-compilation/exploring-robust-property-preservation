From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.
Require Import RobustTraceProperty. 

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section RobustHyperPreservation.


  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Type.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.
  Local Definition hprop__S := hprop trace__S.
  Local Definition hprop__T := hprop trace__T.

  
  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition beh__T := beh Target_Semantics. 
  Local Definition par__S := par Source.
  Local Definition par__T := par Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target. 
  Local Definition rhsat__S := rhsat Source_Semantics.
  Local Definition rhsat__T := rhsat Target_Semantics.
  
  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work 

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  (* these are still maps between properties *)
  Variable σ__π : prop__T -> prop__S.
  Variable τ__π : prop__S -> prop__T.

  Local Definition σ : hprop__T -> hprop__S := lift σ__π.
  Local Definition τ : hprop__S -> hprop__T := lift τ__π.
  

  Definition σRhP (P : par__S) (H__T : hprop__T) :=
    rhsat__S P (σ H__T) -> rhsat__T (P ↓) H__T.

  Definition σRHP := forall P H__T, σRhP P H__T.

  Lemma contra_σRhP (P : par__S) (H__T : hprop__T) :
    (σRhP P H__T) <->  ((exists C__T, ~ H__T (beh__T (plug__T (P↓) C__T))) ->
                   (exists C__S, ~ (σ H__T) (beh__S ( plug__S  P C__S)))).
  Proof.
    rewrite /σRhP. by rewrite [_ -> _] contra !neg_rhsat.
  Qed.

  Lemma contra_σRTP :
    σRHP <-> (forall P H__T,  ((exists C__T, ~ H__T (beh__T (plug__T (P↓) C__T))) ->
                      (exists C__S, ~ (σ H__T) (beh__S ( plug__S  P C__S))))).
  Proof.
    rewrite /σRHP.
    split => H P H__T; by move/contra_σRhP: (H P H__T).
  Qed.

  Definition τRhP (P : par__S) (H__S : hprop__S) :=
    rhsat__S P H__S -> rhsat__T (P ↓) (τ H__S).

  Definition τRHP := forall P H__S, τRhP P H__S.

  Lemma contra_τRhP (P : par__S) (H__S : hprop__S) :
    (τRhP P H__S) <-> ((exists C__T, ~ (τ H__S) (beh__T (plug__T (P↓) C__T))) ->
                 (exists C__S, ~  H__S (beh__S (plug__S P C__S)))).
  Proof.
    rewrite /τRhP. by rewrite [_ -> _] contra !neg_rhsat.
  Qed.

  Lemma contra_τRHP :
    τRHP <-> (forall P H__S, ((exists C__T, ~ (τ H__S) (beh__T (plug__T (P↓) C__T))) ->
                 (exists C__S, ~  H__S (beh__S (plug__S P C__S))))).
  Proof.
    rewrite /τRHP.
    split => H P H__S; by move/contra_τRhP: (H P H__S).
  Qed.

End RobustHyperPreservation.
