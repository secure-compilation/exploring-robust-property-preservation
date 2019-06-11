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
Require Import NonRobustDef.
Require Import NonRobustHyperDef.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section HyperCriterion.

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
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition sat__S := sat Source_Semantics.
  Local Definition sat__T := sat Target_Semantics.
  Local Definition hsat__S := hsat Source_Semantics.
  Local Definition hsat__T := hsat Target_Semantics.

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).

  Variable rel : trace__S -> trace__T -> Prop.

  Local Definition adjunction :=  induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.

  Local Definition τP := τTP compilation_chain
                             Source_Semantics Target_Semantics
                             τ'. 

  Local Definition σP := σTP compilation_chain
                             Source_Semantics Target_Semantics
                             σ'. 
  
  
  Local Definition τHP := τHP compilation_chain
                              Source_Semantics Target_Semantics
                              τ'.

  Local Definition σHP := σHP compilation_chain
                          Source_Semantics Target_Semantics
                          σ'.


  Definition tilde_HC :=  forall W t__T, beh__T (W ↓) t__T <-> (exists t__S, rel t__S t__T /\ beh__S W t__S).

  Definition tilde_HC' := forall W, beh__T (W ↓) = τ' (beh__S W).

  Lemma tilde_HC_HC' : tilde_HC' <-> tilde_HC.
  Proof.
    split => Htilde W.
    rewrite (Htilde W). by firstorder.
    apply functional_extensionality => t__T. apply: prop_extensionality.
    rewrite (Htilde W). by firstorder.
  Qed.

  Theorem tilde_HC_τHP : tilde_HC <-> τHP.
  Proof.
    rewrite -tilde_HC_HC'. split.
    - move => H_tilde W h__S. now exists (beh__S W).
    - move => H_τHP W. specialize (H_τHP W (fun π__S => π__S = beh__S W)).
      have Hfoo : hsat__S W (fun π__S => π__S = beh__S W) by auto.
      destruct (H_τHP Hfoo) as [bs [Heq H]]. subst. exact H.
  Qed.

  (*CA's TODO : relation between tilde_HC and σHP*)

End HyperCriterion.