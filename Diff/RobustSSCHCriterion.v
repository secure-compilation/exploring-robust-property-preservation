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
Require Import RobustSSCHPreservation.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section RobustSSCHCriterion.

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

  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.
  
  Variable rel : trace__S -> trace__T -> Prop.

  Local Definition adjunction :=  induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.

  Definition rel_RSCHC := forall P C__T, exists C__S,
       ( forall t, sem__T (plug__T (P ↓) C__T) t -> exists s, rel s t /\ sem__S (plug__S P C__S) s).

  Local Definition sCl_σ : hprop__T -> hprop__S := sCl_σ σ'.
  Local Definition sCl_τ : hprop__S -> hprop__T := sCl_τ τ'. 
  
  Local Definition sCl_τRhP := sCl_τRhP compilation_chain
                                        Source_Semantics Target_Semantics
                                        τ'.


  Local Definition sCl_σRhP := sCl_σRhP compilation_chain
                                        Source_Semantics Target_Semantics
                                        σ'.


  Lemma sCl_σRhP_sCl_τRhP : (forall (P : par__S) (H__T : hprop__T), SSC H__T ->  sCl_σRhP P H__T) <->
                            (forall (P : par__S) (H__S : hprop__S), SSC H__S -> sCl_τRhP P H__S).
  Proof.         
    split.
    + move => Hσ P H__S ssc_H rsat_source. 
      have rsat_sigma_tau : rhsat__S P (sCl_σ (sCl_τ H__S)).  
      { apply: rhsat_upper_closed. exact rsat_source.
        apply: Galois_snd_lift. exact rel_adjunction_law. exact ssc_H. }       
      have τ_ssc : SSC (sCl_τ H__S) by apply: sCl_SCH.
      exact (Hσ P (sCl_τ H__S) τ_ssc rsat_sigma_tau).  
    + move => Hτ P H__T ssc_H rsat_source.
      have h_ssc: SSC (sCl_σ H__T) by apply: sCl_SCH.
      move: (Hτ P (sCl_σ H__T) h_ssc rsat_source).
      move => HHH. eapply rhsat_upper_closed. exact HHH.
      apply: Galois_fst_lift; eauto. exact rel_adjunction_law. 
  Qed.

  Theorem rel_RSCHC_sClτRSCHP : rel_RSCHC <-> (forall (P : par__S) (H__S : hprop__S), SSC H__S -> sCl_τRhP P H__S).
  Proof.
    split. 
    - move => Htilde P H H_ssc. setoid_rewrite contra_τRhP.
      move => [C__T Hsem].  
      move: (Htilde P C__T) => [C__S HH]. exists C__S => Hfalse.
      apply: Hsem. 
      exists (τ' (beh__S (plug__S P C__S))). split.
      + by exists (beh__S (plug__S P C__S)). 
      + move => t Ht. destruct (HH t Ht) as [s [Hs1 Hs2]]. now exists s.
    - move => Hτ P Ct.
      have Hssc : SSC (fun b: prop__S =>  ~ beh__T (plug__T (P↓) Ct) ⊆ τ' b).
      { move => b1 Hb1 b2 b1_b2 Hb2. apply: Hb1. firstorder. }    
      specialize (Hτ P (fun b: prop__S =>  ~ beh__T (plug__T (P↓) Ct) ⊆ τ' b) Hssc).
      apply contra in Hτ. move: Hτ. rewrite !neg_rhsat. 
      move => [Cs Hbeh]. move/NNPP: Hbeh. 
      exists Cs => t Hsem_t. move: (Hbeh t Hsem_t). firstorder.
      move => Hf. specialize (Hf Ct).
      destruct Hf as [b' [Hb' Hbb]]. destruct Hb' as [bs [Hbs1 Hbs2]]. now subst.  
  Qed.    

  Theorem rel_RTC_σRTP : rel_RSCHC <-> (forall (P : par__S) (H__T : hprop__T), SSC H__T ->  sCl_σRhP P H__T).
  Proof. by rewrite sCl_σRhP_sCl_τRhP rel_RSCHC_sClτRSCHP. Qed.

End RobustSSCHCriterion.
