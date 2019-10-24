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
Require Import RobustHyperProperty.

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section RobustSSCHPreservation.


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
 (* CA: don't understand why this does not work

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  (* these are still maps between properties *)
  Variable σ__π : prop__T -> prop__S.
  Variable τ__π : prop__S -> prop__T.

  Definition sCl_σ : hprop__T -> hprop__S := (uco (@ssch_uco trace__S)) ∘ (lift σ__π).
  Definition sCl_τ : hprop__S -> hprop__T := (uco (@ssch_uco trace__T)) ∘ (lift τ__π).

  Definition sCl_σRhP (P : par__S) (H__T : hprop__T) :=
    rhsat__S P (sCl_σ H__T) -> rhsat__T (P ↓) H__T.

  Lemma contra_σRhP (P : par__S) (H__T : hprop__T) :
    (sCl_σRhP P H__T) <->  ((exists C__T, ~ H__T (beh__T (plug__T (P↓) C__T))) ->
                   (exists C__S, ~ (sCl_σ H__T) (beh__S ( plug__S  P C__S)))).
  Proof.
    rewrite /sCl_σRhP. by rewrite [_ -> _] contra !neg_rhsat.
  Qed.

  Definition sCl_τRhP (P : par__S) (H__S : hprop__S) :=
    rhsat__S P H__S -> rhsat__T (P ↓) (sCl_τ H__S).


  Lemma contra_τRhP (P : par__S) (H__S : hprop__S) :
    (sCl_τRhP P H__S) <-> ((exists C__T, ~ (sCl_τ H__S) (beh__T (plug__T (P↓) C__T))) ->
                 (exists C__S, ~  H__S (beh__S (plug__S P C__S)))).
  Proof.
    rewrite /sCl_τRhP. by rewrite [_ -> _] contra !neg_rhsat.
  Qed.


  Lemma Galois_fst_lift (Hadj : Adjunction_law τ__π σ__π) :
    forall (H__T : hprop__T), SSC H__T ->
       (sCl_τ (sCl_σ (H__T)) ⊆ H__T).
  Proof.
    move => H H_ssc b τ_σ_H_b.
    unfold sCl, lift in τ_σ_H_b.
    destruct τ_σ_H_b as [b' [[b2 [cond b'_eq]] b_b']]. subst.
    destruct cond as [b' [[b2' [H_b2' b'_eq]] b2_b']]. subst.
    move/Hadj: b2_b' => b2_b'. have b_b2': b ⊆ b2' by firstorder.
      by apply: (H_ssc b2').
  Qed.

  Lemma Galois_snd_lift (Hadj : Adjunction_law τ__π σ__π) :
    forall (H__S : hprop__S), SSC H__S ->
                     H__S ⊆ (sCl_σ (sCl_τ H__S)).
  Proof.
    move => H H_ssc b H_b.
    unfold sCl, lift. exists (σ__π (τ__π b)). split.
    - exists (τ__π b). split; auto.
      + exists (τ__π b). split; auto.
        ++ by exists b.
                + move/Galois_equiv: Hadj. move => [H_mono1 [H_mono2 [G1 G2]]].
                  apply: G1.
  Qed.

  Theorem τRSCHP_σRSCHP (Hadj: Adjunction_law τ__π σ__π):
    ((forall P (H__T: hprop__T), SSC H__T ->  sCl_σRhP P H__T) <->
     (forall P (H__S: hprop__S), SSC H__S ->  sCl_τRhP P H__S)).
  Proof.
   split.
    - move => Hσ P H__S H_ssc rsat_source.
      have rsat_sigma_tau : rhsat__S P (sCl_σ (sCl_τ H__S)).
      { apply: rhsat_upper_closed. exact rsat_source.
          by apply: Galois_snd_lift. }
      have τ_ssc : SSC (sCl_τ H__S) by apply: sCl_SCH.
      exact (Hσ P ((sCl_τ H__S)) τ_ssc rsat_sigma_tau).
    - move => Hτ P H__T H_ssc rsat_source.
      have h_ssc: SSC (sCl_σ H__T) by apply: sCl_SCH.
      move: (Hτ P (sCl_σ H__T) h_ssc rsat_source).
      move => HHH. eapply rhsat_upper_closed. exact HHH.
        by apply: Galois_fst_lift.
  Qed.


End RobustSSCHPreservation.
