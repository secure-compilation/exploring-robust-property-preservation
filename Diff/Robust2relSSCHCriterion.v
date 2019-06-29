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
Require Import Robust2relSSCHPreservation. 

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section Robust2relCrit.

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
  Local Definition beh__S := beh Source_Semantics.
  Local Definition beh__T := beh Target_Semantics. 
  Local Definition par__S := par Source.
  Local Definition par__T := par Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target. 
  Local Definition rhsat__S := rhsat2 Source_Semantics.
  Local Definition rhsat__T := rhsat2 Target_Semantics.
  
  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work 

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  Variable rel : trace__S -> trace__T -> Prop.

  (* __π to highlights these maps are mappings between properties  *)
  Local Definition σ__π : (trace__T -> Prop) -> (trace__S -> Prop) :=
                       γ (@induced_connection (trace__T) (trace__S) rel). 

  Local Definition τ__π : (trace__S -> Prop) -> (trace__T -> Prop) :=
                       α (@induced_connection (trace__T) (trace__S) rel).

  Local Definition induced_adj : Adjunction_law τ__π σ__π := 
    adjunction_law (induced_connection rel).

  Lemma τ__π_mono : monotone τ__π. 
  Proof. move: induced_adj. rewrite Galois_equiv. easy. Qed. 

  Local Definition σ : (prop__T * prop__T -> Prop) -> (prop__S * prop__S -> Prop) := prod_σ σ__π.
  Local Definition τ : (prop__S * prop__S -> Prop) -> (prop__T * prop__T -> Prop) := prod_τ τ__π.
  

  Local Definition sCl_σR2rhP := sCl_σR2rhP compilation_chain
                                           Source_Semantics Target_Semantics
                                           σ__π.

  Local Definition sCl_τR2rhP := sCl_τR2rhP compilation_chain
                                        Source_Semantics Target_Semantics
                                        τ__π. 

  Definition rel_R2rSCHC : Prop :=
    forall C__T P1 P2, exists C__S,
        forall t1 t2, sem__T (plug__T (P1 ↓) C__T) t1 ->
                  sem__T (plug__T (P2 ↓) C__T) t2 ->
           exists s1 s2, rel s1 t1 /\
                     rel s2 t2 /\
                     sem__S (plug__S P1 C__S) s1 /\
                     sem__S (plug__S P2 C__S) s2.

  Lemma rel_R2rSCHC_conclusion (C__T : ctx__T) (P1 P2 : par__S) (C__S : ctx__S):
    (forall t1 t2, sem__T (plug__T (P1 ↓) C__T) t1 ->
               sem__T (plug__T (P2 ↓) C__T) t2 ->
           exists s1 s2, rel s1 t1 /\
                     rel s2 t2 /\
                     sem__S (plug__S P1 C__S) s1 /\
                     sem__S (plug__S P2 C__S) s2 ) <->
    (beh__T (plug__T (P1 ↓) C__T)) ⊆ τ__π (beh__S (plug__S P1 C__S)) /\
    (beh__T (plug__T (P2 ↓) C__T)) ⊆ τ__π (beh__S (plug__S P2 C__S)).
  Proof.
    split.
    + move => lhs. split.
         move => t1 Hsem1. destruct (non_empty_sem Target_Semantics (plug__T (P2 ↓) C__T)) as [t2 Hsem2].
         destruct (lhs t1 t2 Hsem1 Hsem2) as [s1 [s2 [rel1 [rel2 [Hsem1' Hsem2']]]]].
         now exists s1. 
       move => t2 Hsem2. destruct (non_empty_sem Target_Semantics (plug__T (P1 ↓) C__T)) as [t1 Hsem1].
       destruct (lhs t1 t2 Hsem1 Hsem2) as [s1 [s2 [rel1 [rel2 [Hsem1' Hsem2']]]]].
       now exists s2.
    + move => [H1 H2] t1 t2 Hsem1 Hsem2.
      move: (H1 t1 Hsem1) (H2 t2 Hsem2). rewrite /τ__π /α /induced_connection /low_rel /=.
        by firstorder.
   Qed.      
      
  Theorem rel_R2rSCHC_sCl_τR2rSCHP :
    rel_R2rSCHC <->
    (forall (P1 P2 : par__S) S, SCH2 S -> sCl_τR2rhP P1 P2 S).
  Proof.
    split. 
    - move => Htilde P1 P2 S S_ssc. setoid_rewrite contra_τR2rhP.
      move => [C__T Hsem].  
      move: (Htilde C__T P1 P2) => [C__S HH].
      exists C__S => Hfalse.
      apply: Hsem. 
      exists (τ__π (beh__S (plug__S P1 C__S))), (τ__π (beh__S (plug__S P2 C__S))). split.
      + by exists (beh__S (plug__S P1 C__S)), (beh__S (plug__S P2 C__S)). 
      + by rewrite //= -rel_R2rSCHC_conclusion. 
    - move => Hτ C__T P1 P2.
      have Hssc : SCH2 (fun b: prop__S * prop__S =>  ~ (beh__T (plug__T (P1 ↓) C__T) ⊆ τ__π (fst b) /\
                                                  beh__T (plug__T (P2 ↓) C__T) ⊆ τ__π (snd b))).
      { rewrite /SCH2. move => β1 β2 β1' β2' Hb  b1_b1 b2_b2 [Hf1 Hf2]. 
        apply: Hb. split;                               
        apply: subset_trans; eauto; rewrite /=; by apply: τ__π_mono. }     
      specialize (Hτ P1 P2 _ Hssc).
      apply contra in Hτ. move: Hτ. rewrite !neg_rhsat2 /=.  
      move => [Cs Hbeh]. exists Cs.  
      rewrite rel_R2rSCHC_conclusion. by move/NNPP: Hbeh.
      rewrite neg_rhsat2. exists C__T. move => [b1[ b2 Hf]].
      move: Hf. rewrite /prod_τ /=. move => [[π__S [π__S' [Heq1 [Heq2 Hn]]]] [H1 H2]].
      subst. by apply: Hn. 
  Qed.
  
  Theorem rel_R2rTC_σR2rTP :
    rel_R2rSCHC <->
    (forall (P1 P2 : par__S) T, SCH2 T -> sCl_σR2rhP P1 P2 T). 
  Proof.
    setoid_rewrite  (Adj_sCl_σR2rSCHP_iff_sCl_τR2rSCHP _ _ _ induced_adj).
    by rewrite rel_R2rSCHC_sCl_τR2rSCHP.  
  Qed. 
    
End Robust2relCrit.