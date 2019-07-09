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
Require Import NonRobustHyperDef.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section SSCHPreservation.


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

  Local Notation "W ↓" := (cmp W) (at level 50).
 (* CA: don't understand why this does not work

   Local Notation " C [ W ] " := (plug _  W C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  (* these are still maps between properties *)
  Variable σ__π : prop__T -> prop__S.
  Variable τ__π : prop__S -> prop__T.

  Definition sCl_σ : hprop__T -> hprop__S := (uco (@ssch_uco trace__S)) ∘ (lift σ__π).
  Definition sCl_τ : hprop__S -> hprop__T := (uco (@ssch_uco trace__T)) ∘ (lift τ__π).

  Definition sCl_σhP (W : prg__S) (H__T : hprop__T) :=
    hsat__S W (sCl_σ H__T) -> hsat__T (W ↓) H__T.

  Definition sCl_τhP (W : prg__S) (H__S : hprop__S) :=
    hsat__S W H__S -> hsat__T (W ↓) (sCl_τ H__S).


  (*TODO: bring this to Properties.v *)

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

  Theorem sCl_τSCHP_sCl_σSCHP (Hadj: Adjunction_law τ__π σ__π):
    ((forall W (H__T: hprop__T), SSC H__T ->  sCl_σhP W H__T) <->
     (forall W (H__S: hprop__S), SSC H__S ->  sCl_τhP W H__S)).
  Proof.
   split. Locate rhsat_upper_closed.
    - move => Hσ W H__S H_ssc rsat_source.
      have rsat_sigma_tau : hsat__S W (sCl_σ (sCl_τ H__S)).
      { apply: hsat_upper_closed. exact rsat_source.
          by apply: Galois_snd_lift. }
      have τ_ssc : SSC (sCl_τ H__S) by apply: sCl_SCH.
      exact (Hσ W ((sCl_τ H__S)) τ_ssc rsat_sigma_tau).
    - move => Hτ W H__T H_ssc rsat_source.
      have h_ssc: SSC (sCl_σ H__T) by apply: sCl_SCH.
      move: (Hτ W (sCl_σ H__T) h_ssc rsat_source).
      move => HHH. eapply hsat_upper_closed. exact HHH.
        by apply: Galois_fst_lift.
  Qed.


End SSCHPreservation.