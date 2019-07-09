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
Require Import NonRobustTraceCriterion.

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


  Definition rel_HC :=  forall W t__T, beh__T (W ↓) t__T <-> (exists t__S, rel t__S t__T /\ beh__S W t__S).

  Lemma rel_HC' : rel_HC <-> forall W, beh__T (W ↓) = τ' (beh__S W).
    split => Hrel W.
    apply functional_extensionality => t__T. apply: prop_extensionality.
    rewrite (Hrel W). by firstorder.
    rewrite (Hrel W). by firstorder. 
  Qed.

  Theorem rel_HC_τHP : rel_HC <-> τHP.
  Proof.
    rewrite rel_HC'. split.
    - move => H_rel W h__S. now exists (beh__S W).
    - move => H_τHP W. specialize (H_τHP W (fun π__S => π__S = beh__S W)).
      have Hfoo : hsat__S W (fun π__S => π__S = beh__S W) by auto.
      destruct (H_τHP Hfoo) as [bs [Heq H]]. subst. exact H.
  Qed.

  (*CA: if τ ⇆ σ is an insertion then
        tilde_HC =>  σHP 
        but not able to prove the vicerversa holds  
        (quite convinced it is not true)
  *)

  Lemma rel_HC_σHP : (Insertion_snd τ' σ') ->
    rel_HC -> σHP.
  Proof.
    rewrite rel_HC' => HIns Hrel W H__T [b__T [bt_HT Heq]].
    move: (Hrel W). rewrite /beh__T /beh__S Heq HIns. 
    move => Heq__T. now subst.        
  Qed. 

  (****************************************************************)

  (* rel_TC /\ rel_TC_fwd -> rel_HC ? *)

  Local Definition rel_TC := rel_TC compilation_chain
                                    Source_Semantics Target_Semantics
                                    rel.

  Local Definition rel_FC1 := rel_FC1 compilation_chain
                                      Source_Semantics Target_Semantics
                                      rel.

  Local Definition rel_FC2 := rel_FC2 compilation_chain
                                      Source_Semantics Target_Semantics
                                      rel. 

  (* under the assumption rel is a total function from source to target traces
     HC comes as consequence of TC and FC
   *)
  Theorem rel_total_map_TC_plus_FC1_HC :
   (forall s, exists! t, rel s t) ->
    rel_TC -> rel_FC1 -> rel_HC.  
  Proof.
   setoid_rewrite rel_TC'. setoid_rewrite rel_FC1'. 
   rewrite rel_HC' => rel_map bcc fcc W.
   apply: mutual_inclusion. 
   + by apply: bcc. 
   + rewrite rel_adjunction_law => s behWs t rel_s_t.
     move: (fcc W s behWs). move => [t' [rel_s_t' beh_cmpW_t']].
     have Heq: t = t'.
     { move: (rel_map s). move => [t0 [rel_s_t0 eq_t0]].
         by rewrite -(eq_t0 t rel_s_t) -(eq_t0 t' rel_s_t'). }
       by rewrite Heq.
   Qed.  

  Theorem TC_plus_FC2_HC :
    rel_TC -> rel_FC2 -> rel_HC.
  Proof.
    setoid_rewrite rel_TC'. setoid_rewrite rel_FC2'.
    rewrite rel_HC' => bcc fcc W.
    apply: mutual_inclusion.
    + exact (bcc W).
    + rewrite rel_adjunction_law. exact (fcc W).
  Qed.

End HyperCriterion.