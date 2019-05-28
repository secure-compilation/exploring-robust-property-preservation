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
Require Import NonRobustDef.
Require Import NonRobustHyperDef.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section SafetyCriterion.

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
  

  Local Definition τHP := τHP compilation_chain
                              Source_Semantics Target_Semantics
                              τ'.
  
  
  Local Definition σHP := σHP compilation_chain
                              Source_Semantics Target_Semantics
                              σ'.

  Definition tilde_HC :=  forall W, beh__T (W ↓) = τ' (beh__S W). 
                                 
    
  Theorem tilde_HC_τHP : tilde_HC <-> τHP.
  Proof.
    split.
    - move => H_tilde W h__S. now exists (beh__S W). 
    - move => H_τHP W. specialize (H_τHP W (fun π__S => π__S = beh__S W)).
      have Hfoo : hsat__S W (fun π__S => π__S = beh__S W) by auto.                           
      destruct (H_τHP Hfoo) as [bs [Heq H]]. subst. exact H.  
  Qed.

  Theorem tilde_HC_σHP : Insertion_snd τ' σ' ->  tilde_HC <-> σHP.
  Proof.
    move => H_ins. split.
    - rewrite tilde_HC_τHP. by apply: Insetion_τHP_σHP. 
    - setoid_rewrite contra_σHP => H_σHP W.
      have Hfoo: ~ hsat__T (W ↓) (fun π__T =>  π__T <> (beh__T (W ↓))) by auto.  
      specialize (H_σHP W (fun π__T =>  π__T <> (beh__T (W ↓))) Hfoo); clear Hfoo.
      have Hfoo: ~ (lift τ') ((lift σ')  (fun π__T =>  π__T <> (beh__T (W ↓)))) (τ' (beh__S W)). 
      { admit. }
      have Hfoofoo: (lift τ') ((lift σ')  (fun π__T =>  π__T <> (beh__T (W ↓)))) = (fun π__T =>  π__T <> (beh__T (W ↓))).
      { admit. }
      move: Hfoo. rewrite Hfoofoo -dne. congruence.   
  Admitted.     
    
         
      
      
End SafetyCriterion. 