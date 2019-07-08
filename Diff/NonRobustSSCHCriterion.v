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
Require Import NonRobustSSCHPreservation.
Require Import NonRobustTraceCriterion.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section SSCHCriterion.

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
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target. 
  Local Definition hsat__S := hsat Source_Semantics.
  Local Definition hsat__T := hsat Target_Semantics.
  
  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).

  Variable rel : trace__S -> trace__T -> Prop.

  Local Definition adjunction :=  induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.

  Lemma τ_mono : monotone τ'. 
  Proof. move/Galois_equiv: rel_adjunction_law. by move => [H1 H2]. Qed.
  
  Definition rel_TC : Prop := rel_TC  compilation_chain
                                   Source_Semantics Target_Semantics
                                   rel. 
    
  Local Definition sCl_σ : hprop__T -> hprop__S := sCl_σ σ'.
  Local Definition sCl_τ : hprop__S -> hprop__T := sCl_τ τ'. 
  
  Local Definition sCl_τhP := sCl_τhP compilation_chain
                                      Source_Semantics Target_Semantics
                                      τ'.


  Local Definition sCl_σhP := sCl_σhP compilation_chain
                                      Source_Semantics Target_Semantics
                                      σ'.


  Lemma sCl_σhP_sCl_τhP : (forall (W : prg__S) (H__T : hprop__T), SSC H__T ->  sCl_σhP W H__T) <->
                          (forall (W : prg__S) (H__S : hprop__S), SSC H__S -> sCl_τhP W H__S).
  Proof.         
    split.
    + move => Hσ P H__S ssc_H rsat_source. 
      have rsat_sigma_tau : hsat__S P (sCl_σ (sCl_τ H__S)).  
      { apply: hsat_upper_closed. exact rsat_source.
        apply: Galois_snd_lift. exact rel_adjunction_law. exact ssc_H. }       
      have τ_ssc : SSC (sCl_τ H__S) by apply: sCl_SCH.
      exact (Hσ P (sCl_τ H__S) τ_ssc rsat_sigma_tau).  
    + move => Hτ P H__T ssc_H rsat_source.
      have h_ssc: SSC (sCl_σ H__T) by apply: sCl_SCH.
      move: (Hτ P (sCl_σ H__T) h_ssc rsat_source).
      move => HHH. eapply hsat_upper_closed. exact HHH.
      apply: Galois_fst_lift; eauto. exact rel_adjunction_law. 
  Qed.

  Theorem rel_TC_sClτSCHP : rel_TC <-> (forall (P : prg__S) (H__S : hprop__S), SSC H__S -> sCl_τhP P H__S).
  Proof.
    setoid_rewrite rel_TC'. 
    split. 
    - move => Htilde P H H_ssc Hsrc. 
      exists (τ' (beh__S P)). split.
      + rewrite /lift. exists (beh__S P).
        split; auto. exact: (Htilde P).  
    - move => Hτ W.
      have Hssc: SSC (fun b: prop__S => b ⊆ beh__S W) by firstorder. 
      have Hfoo: hsat__S W (fun b: prop__S => b ⊆ beh__S W) by rewrite /hsat__S.  
      move: (Hτ W _ Hssc Hfoo).
      move => [b__T [[b__S [H1 H2]] H3]]. subst. 
      apply: subset_trans.
      exact H3. by apply: τ_mono.
  Qed.
 
  Theorem rel_TC_sCl_σRSCHP : rel_TC <-> (forall (W : prg__S) (H__T : hprop__T), SSC H__T ->  sCl_σhP W H__T).
  Proof. by rewrite sCl_σhP_sCl_τhP rel_TC_sClτSCHP. Qed.

End SSCHCriterion.
