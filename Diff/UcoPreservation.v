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

(* Every time we can express a Class Ξ via an upper closed operator ξ
   we have that γRΞP is equivalent to (ξ ∘ τ)RTP. 
   
   for instance we can express the class of Safety and Dense properties using 
   the uco Cl. 

*)

Section Closure_Operators_Preservation.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation 
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Set.
  
  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.
  
  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T. 

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.   
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition sat__S := sat Source_Semantics. 
  Local Definition sat__T := sat Target_Semantics. 
  
  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).
  
  Variable σ : prop__T -> prop__S. 
  Variable τ : prop__S -> prop__T.

  Variable ϕ_op : (@Uco trace__T). 

  Local Definition ϕ := uco ϕ_op.

  Check σP. 
  
  Local Definition σP := σP compilation_chain
                            Source_Semantics Target_Semantics
                            σ.

  (* ϕ ∘ τ *)
  Local Definition ϕ_τP := τP compilation_chain
                              Source_Semantics Target_Semantics
                              (ϕ ∘ τ). 
  
  Local Definition ϕ_τTP := forall W π__S, ϕ_τP W π__S. 
  
  Lemma uco_adjuncts' :
    Adjunction_law τ σ -> 
    ( (forall W (π__T : prop__T),  σP W (ϕ π__T)) <->                    
      ϕ_τTP ).
  Proof. 
    rewrite Galois_equiv. move => [mono_σ [mono_τ [G1 G2]]].
    split => H_p W π sat_src.  
    + have H: sat__S W (σ (ϕ (τ π))).
      { apply: sat_upper_closed. exact: sat_src.
        apply: subset_trans. by apply: G1. 
        apply: mono_τ. exact: (ext ϕ_op). }  
      move: (H_p W (ϕ (τ π))). firstorder. 
    + have H: sat__T (W ↓) (ϕ π).
      { move: (H_p W _ sat_src) => H.
        apply: sat_upper_closed. exact: H.
        have Hfoo : ϕ π = ϕ (ϕ π) by rewrite /ϕ (idmp ϕ_op). 
        move => t Hfoo_t. rewrite Hfoo.
        move: t Hfoo_t.
        apply: mono. by apply: G2. }
      exact: H. 
  Qed.

  Lemma uco_aux  :
    (forall W (π__T : prop__T),  σP W (ϕ π__T)) <->
    (forall W (π__T : prop__T),  ((lift ϕ) (@h_true trace__T)) π__T -> σP W π__T).
  Proof.
    split => H_p W π.
    + move => [b [hb Cb]] sat_src. subst.
        by move: (H_p W b sat_src).  
    + move => sat_src.
      have H: (lift ϕ (@h_true trace__T)) (ϕ π) by now exists π. 
       by move: (H_p W (ϕ π) H sat_src). 
  Qed.   
  
 Theorem uco_adjuncts :
  Adjunction_law τ σ ->
  ( (forall W (π__T : prop__T),  ((lift ϕ) (@h_true trace__T) π__T) -> σP W π__T) <->                    
     ϕ_τTP ).
 Proof.
  move => H_adj. rewrite -uco_adjuncts'.
    by rewrite -uco_aux. assumption.
Qed.

  
End Closure_Operators_Preservation. 