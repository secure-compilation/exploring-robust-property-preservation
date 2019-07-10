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
Require Import RobustHyperProperty.
Require Import RobustTraceCriterion.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section RobustHyperCriterion.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Set.

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
  Local Definition ctx__S := ctx Source.
  Local Definition par__T := par Target.
  Local Definition ctx__T := ctx Target.
  Local Definition rsat__S := rsat Source_Semantics.
  Local Definition rsat__T := rsat Target_Semantics.
  Local Definition hsat__S := hsat Source_Semantics.
  Local Definition rhsat__S := rhsat Source_Semantics.
  Local Definition rhsat__T := rhsat Target_Semantics.

  Local Definition cmp := compile_par Source Target compilation_chain.
  Local Definition plug__S := plug Source.
  Local Definition plug__T := plug Target.
  
  Local Notation "P ↓" := (cmp P) (at level 50).

  Variable rel : trace__S -> trace__T -> Prop.

  Local Definition adjunction :=  induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.

  Local Definition τRhP := τRhP compilation_chain
                              Source_Semantics Target_Semantics
                              τ'.

  Local Definition σRhP := σRhP compilation_chain
                                Source_Semantics Target_Semantics
                                σ'.


  Local Definition τRHP := τRHP compilation_chain
                              Source_Semantics Target_Semantics
                              τ'.

  Local Definition σRHP := σRHP compilation_chain
                               Source_Semantics Target_Semantics
                               σ'.

  Definition rel_RHC :=  forall P C__T, exists C__S,
                         forall t__T, (beh__T (plug__T (P ↓) C__T) t__T <->
                                 (exists t__S, rel t__S t__T /\ beh__S (plug__S P C__S) t__S)).

  Lemma rel_RHC' : rel_RHC <-> forall P C__T, exists C__S, (beh__T (plug__T (P ↓) C__T) = τ' (beh__S (plug__S P C__S))).
    split => Hrel P C__T.
    destruct (Hrel P C__T) as [C__S Hrel'].
    exists C__S. apply functional_extensionality => t__T. apply: prop_extensionality.
    rewrite Hrel'. by firstorder.
    destruct (Hrel P C__T) as [C__S Hrel'].
    rewrite Hrel'. by firstorder.
  Qed.

  Theorem rel_RHC_τRHP : rel_RHC <-> τRHP.
  Proof.
    rewrite rel_RHC'. split.
    - move => H_rel P h__S H_src C__T.
      destruct (H_rel P C__T) as [C__S H_rel'].
      exists (beh__S (plug__S P C__S)). split.
      + by apply: (H_src C__S). 
      + by rewrite -H_rel'. 
    - move => H_τHP P C__T. specialize (H_τHP P (fun π__S => exists C__S, π__S = beh__S (plug__S P C__S))).
      have Hfoo : rhsat__S P (fun π__S => exists C__S, π__S = beh__S (plug__S P C__S)).
       { move => C__S. by exists C__S. } 
       destruct (H_τHP Hfoo C__T) as [bs [[C__S Heq] H]].
       exists C__S. subst. exact H.
  Qed.

  (*CA: if τ ⇆ σ is an insertion then
        tilde_HC =>  σHP
        but not able to prove the vicerversa holds
        (quite convinced it is not true)
  *)

  Lemma rel_RHC_σRHP : (Insertion_snd τ' σ') ->
    rel_RHC -> σRHP.
  Proof.
    rewrite rel_RHC' => HIns Hrel P H__T Hsrc C__T.
    move: (Hrel P C__T).
    move => [C__S Heq].
    move: (Hsrc C__S). move => [b__t [Hb__T Hσ]].
    have Hfoo: beh__T (plug__T (P ↓) C__T) = b__t.  
    { rewrite Heq.
      have Hfoo' : τ' (beh__S (plug__S P C__S)) = τ' ( σ' b__t) by rewrite -Hσ. 
      move: Hfoo'. by rewrite HIns. } 
    rewrite /hsat.
    have Hstrange: (beh Target_Semantics (plug Target (RobustHyperProperty.cmp compilation_chain P) C__T))= b__t by rewrite -Hfoo.
    now rewrite Hstrange. 
   Qed.

End RobustHyperCriterion.