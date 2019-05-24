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

Section Closure_Operators_Preservation.

 (* Every time we can express a Class Ξ via an upper closed operator ξ
     we have that γΞP is equivalent to (ξ ∘ τ)TP. 
    
     for instance we can express the class of Safety properties using 
     the uco Cl. *)


   Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.
  
  Variable Σ__S Σ__T States__S States__T : Set.
  Variable E__S : Events Σ__S.
  Variable E__T : Events Σ__T.
  Variable S__S : EndState States__S.
  Variable S__T : EndState States__T.

  Local Definition trace__S := trace Σ__S States__S.
  Local Definition trace__T := trace Σ__T States__T.
  Local Definition prop__S := prop Σ__S States__S.
  Local Definition prop__T := prop Σ__T States__T.
  
  Variable sem__S : prg Source -> trace__S -> Prop.
  Variable non_empty_sem__S : forall W, exists s, sem__S W s.   

  Variable sem__T : prg Target -> trace__T -> Prop.
  Variable non_empty_sem__T : forall W, exists t, sem__T W t.   
  
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.

  Local Definition sat__S := sat Source sem__S.
  Local Definition sat__T := sat Target sem__T.
  
  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).
 
   
  (*CA: issue! prop__T : Type but not prop__T : Set! *)
  Variable cl_operator : (Uco prop__T).  

  
  
  Lemma uco_adjuncts_rp' (f: Uco ) :
    Adjunction_law τ σ -> 
    ( (forall W (π__T : prop__T),  σP W ((uco f) π__T)) <->                    
      (τTP ((uco f) ∘ τ))).
  Proof. 
    rewrite Galois_equiv. move => [mono_γ [mono_τ [G1 G2]]].
    split => H_rp P π rsat_src.  
    + have H: rsat P (γ ((uco f) (τ π))).
      { apply: rsat_upper_closed. exact: rsat_src.
        apply: (@prop_subset_trans source π (γ (τ π))). by apply: G1. 
        apply: mono_γ. exact: (ext f). }  
      move: (H_rp P (((uco f) (τ π)))). firstorder. 
    + have H: rsat (P ↓) ((uco f) π).
      { move: (H_rp P _ rsat_src) => H.
        apply: rsat_upper_closed. exact: H.
        apply: (@prop_subset_trans target _ ((uco f) (uco f π)) _).
        apply: mono. by apply: G2.
          by rewrite (idmp f). }
      exact: H. 
  Qed.

End Closure_Operators_Preservation. 