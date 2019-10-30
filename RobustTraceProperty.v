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

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section RobustPreservation.


  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Type.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition par__S := par Source.
  Local Definition par__T := par Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target.
  Local Definition rsat__S := rsat Source_Semantics.
  Local Definition rsat__T := rsat Target_Semantics.

  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  Variable σ : prop__T -> prop__S.
  Variable τ : prop__S -> prop__T.

  Definition σRP (P : par__S) (π__T : (trace__T -> Prop)) :=
    rsat__S P (σ π__T) -> rsat__T (P ↓) π__T.

  Definition σRTP := forall P π__T, σRP P π__T.

  Lemma contra_σRP (P : par__S) (π__T : prop__T) :
    (σRP P π__T) <->  ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (π__T t)) ->
                   (exists C__S s, sem__S ( plug__S  P C__S) s /\ ~ (σ π__T) s)).
  Proof.
    rewrite /σRP. by rewrite [_ -> _] contra !neg_rsat.
  Qed.

  Lemma contra_σRTP :
    σRTP <-> (forall P π__T, (exists C__T t, sem__T (plug__T (P ↓) C__T) t /\ ~ (π__T t)) ->
                     (exists C__S s, sem__S (plug__S P C__S) s /\ ~ (σ π__T) s)).
  Proof.
    rewrite /σRTP.
    split => H P π__T; by move/contra_σRP: (H P π__T).
  Qed.

  Definition τRP (P : par__S) (π__S : prop__S) :=
    rsat__S P π__S -> rsat__T (P ↓) (τ π__S).

  Definition τRTP := forall P π__S, τRP P π__S.


  Lemma contra_τRP (P : par__S) (π__S : prop__S) :
    (τRP P π__S) <-> ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (τ π__S) t) ->
                 (exists C__S s, sem__S (plug__S P C__S) s /\ ~ π__S s)).
  Proof.
    rewrite /τRP. by rewrite [_ -> _] contra !neg_rsat.
  Qed.

  Lemma contra_τRTP :
    τRTP <-> (forall P π__S, ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (τ π__S) t) ->
                     (exists C__S s, sem__S (plug__S P C__S) s /\ ~ π__S s))).
  Proof.
    rewrite /τRTP.
    split => H P π__S; by move/contra_τRP: (H P π__S).
  Qed.

  Theorem G_σRTP_iff_τRTP :
    (Galois_fst τ σ) -> (Galois_snd τ σ) -> (σRTP <-> τRTP).
  Proof.
    move => G1 G2. split.
    - move => Hσ P πs Hrsat_src. apply: (Hσ P (τ πs)).
      apply: rsat_upper_closed. exact Hrsat_src. by apply: G1.
    - move => Hτ P πt Hrrsat_tgt.
      have H : rsat__T (P ↓) (τ (σ πt)) by apply: Hτ.
      apply: rsat_upper_closed. exact H. by apply: G2.
  Qed.

  Corollary Adj_σRTP_iff_τRTP :
    Adjunction_law τ σ -> (σRTP <-> τRTP).
  Proof.
    rewrite Galois_equiv. move => [ms [mt [G1 G2]]].
      by apply: G_σRTP_iff_τRTP.
  Qed.

  Section General.
    
    Local Definition hprop__S : Type := hprop trace__S.
    Local Definition hprop__T : Type := hprop trace__T. 
    
    Variable X : hprop__S.
    Variable Y : hprop__T.
    
    Variable α : prop__S -> prop__T. 
    Variable γ : prop__T -> prop__S.

    Variable αXY : forall π__S, X π__S -> Y (α π__S).
    Variable γYX : forall π__T, Y π__T -> X (γ π__T).

    Hypothesis γY_mono : forall y1 y2, Y y1 -> Y y2 -> y1 ⊆ y2 -> (γ y1) ⊆ (γ y2).  

    Hypothesis Galois_fst_X_Y :
      forall π__S, X π__S ->  π__S ⊆ γ (α π__S).
    
    Hypothesis Galois_snd_X_Y :
      forall π__T, Y π__T -> α (γ π__T) ⊆ π__T. 

    Definition γRP (P : par__S) (π__T : (trace__T -> Prop)) :=
    rsat__S P (γ π__T) -> rsat__T (P ↓) π__T.

    Definition γRYP := forall P π__T, Y π__T -> γRP P π__T.

    Definition αRP (P : par__S) (π__S : prop__S) :=
    rsat__S P π__S -> rsat__T (P ↓) (α π__S).

    Definition αRXP := forall P π__S, X π__S -> αRP P π__S.

    Lemma γ_α_γ (π__T : prop__T) (Yπ__T : Y π__T): γ (α (γ π__T)) = (γ π__T).
    Proof.  
      apply: mutual_inclusion. 
      - apply: γY_mono.
          by apply: (αXY (γYX Yπ__T)).  
          exact: Yπ__T.
          by apply: Galois_snd_X_Y. 
      - apply: Galois_fst_X_Y.
          by apply: γYX.
    Qed.         
          
    Theorem Generalization_σRTP_iff_τRTP : γRYP <-> αRXP.
    Proof.
      split.
      - move => HγRYP P π__S Xπ__S Hsrc.
        have γHsrc : rsat__S P (γ (α π__S)).
        { apply: rsat_upper_closed. exact: Hsrc.
          by apply: Galois_fst_X_Y. } 
        move: (HγRYP P (α π__S) (αXY Xπ__S) γHsrc).
        by [].   
      - move => HαRXP P π__T Yπ__T Hsrc.
        have Hcancel : γ (α (γ π__T)) = γ π__T by apply: γ_α_γ. 
        move: (γYX (αXY (γYX Yπ__T))).
        rewrite Hcancel => Xγπ__T. 
        move: (HαRXP P (γ π__T) Xγπ__T Hsrc) => Htrg.
        apply: rsat_upper_closed. exact: Htrg. 
        by apply: Galois_snd_X_Y. 
     Qed.
    
  End General.

End RobustPreservation.
