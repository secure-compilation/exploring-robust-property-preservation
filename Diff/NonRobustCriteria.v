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

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section Criteria.

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

  Variable rel : trace__S -> trace__T -> Prop.  
 
  Definition adjunction :=  induced_connection rel. 
  
  Definition τ' : prop__S -> prop__T := α adjunction.
  Definition σ' : prop__T -> prop__S := γ adjunction.

  Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.
  
  Definition rel_TC := forall W t, sem__T (W ↓) t -> exists s, sem__S W s.  

  Check τTP. 
  
  Local Definition τTP := τTP compilation_chain
                              sem__S sem__T
                              τ'.

  Local Definition σTP := σTP compilation_chain
                              sem__S sem__T
                              σ'.


  Lemma σTP_τTP : σTP <-> τTP.
  Proof. apply: Adj_σTP_iff_τTP. by apply: rel_adjunction_law. Qed. 
                                        
    
  Theorem tilde_TC_τTP : rel_TC <-> τTP. 
  Proof. (* TODO: + understand why "rewrite contra_τTP" does not work without arguments 
                  + modify the proof for the robust case
          *)    
(*   rewrite contra_τTP. split.     *)
(*     - move => Htilde P π [Ct [t [Hsemt Hτ]]]. *)
(*       destruct (Htilde P Ct t Hsemt) as [Cs [s [Hrel_s_t Hsems]]].    *)
(*       exists Cs, s. split; auto. move => s_in_π. apply: Hτ. by exists s. *)
(*  - move => Hτ P Ct t Hsemt. specialize (Hτ P (fun s => ~ rel s t)). *)
(*    case: Hτ. *)
(*    { exists Ct, t. split; auto. unfold τ'. move => [s [Hc Hcc]] //=. } *)
(*    move  => Cs [s [Hsems H]]. exists Cs, s. split; auto; by apply: NNPP.                                   *)
  (* Qed. *) Admitted.

  Theorem tilde_TC_σTP : rel_TC <-> σTP.  
  Proof. by rewrite σTP_τTP tilde_TC_τTP. Qed. 
  
  
End Criteria. 