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

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section TracePropertiesCriterion.
  
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

  Variable rel : trace__S -> trace__T -> Prop.  
 
  Local Definition adjunction :=  induced_connection rel. 
  
  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.
  
  Definition rel_TC := forall W t, sem__T (W ↓) t -> exists s, rel s t /\ sem__S W s.  

  Check τTP. 
  
  Local Definition τTP := τTP compilation_chain
                          Source_Semantics Target_Semantics
                          τ'.

  
  Local Definition σTP := σTP compilation_chain
                              Source_Semantics Target_Semantics
                              σ'.


  Lemma σTP_τTP : σTP <-> τTP.
  Proof. apply: Adj_σTP_iff_τTP. by apply: rel_adjunction_law. Qed.   

  
  Theorem tilde_TC_τTP : rel_TC <-> τTP.

  Proof.
    setoid_rewrite contra_τTP. split.
    - move => Htilde W π [t [Hsemt Hτ]].
      destruct (Htilde W t Hsemt) as [s [Hrel_s_t Hsems]].    
      exists s. split; auto. move => s_in_π. apply: Hτ. by exists s. 
    - move => Hτ W t Hsemt. specialize (Hτ W (fun s => ~ rel s t)). 
      case: Hτ. 
      { exists t. split; auto. unfold τ'. move => [s [Hc Hcc]] //=. } 
      move => s [Hsems H]. exists s. split; auto; by apply: NNPP. 
  Qed. 

  Theorem tilde_TC_σTP : rel_TC <-> σTP.  
  Proof. by rewrite σTP_τTP tilde_TC_τTP. Qed. 
  
  
End TracePropertiesCriterion.

