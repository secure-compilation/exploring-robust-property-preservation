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

Section RobustHSafetyPreservation.


  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable T_evs S_evs : Events.
  Variable T_end S_end : Endstates.

  Local Definition trace__S := @trace S_evs S_end.
  Local Definition finpref__S := @finpref S_evs S_end.
  Local Definition trace__T := @trace T_evs T_end.
  Local Definition finpref__T := @finpref T_evs T_end.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.
  Local Definition hprop__S := hprop trace__S.
  Local Definition hprop__T := hprop trace__T.

  Local Definition HSafety__S := @HSafe S_evs S_end.
  Local Definition HSafety__T := @HSafe T_evs T_end.


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

  Definition sCl_σ : hprop__T -> hprop__S := (uco (@ssch_uco (@trace S_evs S_end))) ∘ (lift σ__π).
  Definition hsCl_τ : hprop__S -> hprop__T := (uco (@hsafe_uco T_evs T_end)) ∘ (lift τ__π).

  Definition sCl_σRhP (P : par__S) (H__T : hprop__T) :=
    rhsat__S P (sCl_σ H__T) -> rhsat__T (P ↓) H__T.

  Lemma contra_σRhP (P : par__S) (H__T : hprop__T) :
    (sCl_σRhP P H__T) <->  ((exists C__T, ~ H__T (beh__T (plug__T (P↓) C__T))) ->
                        (exists C__S, ~ (sCl_σ H__T) (beh__S ( plug__S  P C__S)))).
  Proof.
    rewrite /sCl_σRhP. by rewrite [_ -> _] contra !neg_rhsat.
  Qed.

  Definition hsCl_τRhP (P : par__S) (H__S : hprop__S) :=
    rhsat__S P H__S -> rhsat__T (P ↓) (hsCl_τ H__S).


  Lemma contra_τRhP (P : par__S) (H__S : hprop__S) :
    (hsCl_τRhP P H__S) <-> ((exists C__T, ~ (hsCl_τ H__S) (beh__T (plug__T (P↓) C__T))) ->
                 (exists C__S, ~  H__S (beh__S (plug__S P C__S)))).
  Proof.
    rewrite /hsCl_τRhP. by rewrite [_ -> _] contra !neg_rhsat.
  Qed.

  Theorem τRSCHP_σRSCHP (Hadj: Adjunction_law τ__π σ__π):
    ((forall P (H__T: hprop__T), HSafe H__T ->  sCl_σRhP P H__T) <->
     (forall P (H__S: hprop__S), SSC H__S ->  hsCl_τRhP P H__S)).
  Proof.
   move/Galois_equiv: Hadj. move => [mono_tau [mono_sigma [G1 G2]]].
   split.
    - move => Hσ P H__S H_ssc rsat_source.
      have rsat_sigma_tau : rhsat__S P (sCl_σ (hsCl_τ H__S)).
      { apply: rhsat_upper_closed. exact rsat_source.
        move => b__S H_b__S. exists (σ__π (τ__π b__S)).
        split.
        + exists (τ__π b__S). split; auto.
          rewrite /hsCl_τ //= /hsCl => hs Safe_hs Hτ_hs.
          apply: Hτ_hs. by exists b__S.
        + by apply: G1.
      }
      have τ_ssc : HSafe (hsCl_τ H__S) by apply: hsCl_HSafe.
      exact (Hσ P ((hsCl_τ H__S)) τ_ssc rsat_sigma_tau).
    - move => Hτ P H__T H_HSafe rsat_source.
      have h_ssc: SSC (sCl_σ H__T) by apply: sCl_SCH.
      move: (Hτ P (sCl_σ H__T) h_ssc rsat_source).
      move => HHH. eapply rhsat_upper_closed. exact HHH.
      rewrite /hsCl_τ //=.
      rewrite -(hsCl_id_on_HSafe H_HSafe).
      apply: hsCl_mono. rewrite (hsCl_id_on_HSafe H_HSafe).
      move => b__T [b' [H_b' H']]. subst.
      destruct H_b' as [b'' [Hb1 Hb2]].
      have H_ssc : SSC H__T by apply: HSafe_SCH.
      apply: H_ssc.
      have Hfoo : H__T (τ__π b'').
      { destruct Hb1 as [bb [Hbb1 Hbb2]]. subst.
         have H_ssc : SSC H__T by apply: HSafe_SCH.
        apply: H_ssc. exact Hbb1. by apply: G2. }
      exact Hfoo. by apply: mono_tau.
  Qed.


End RobustHSafetyPreservation.
