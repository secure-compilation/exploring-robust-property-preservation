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
Require Import Def.
Require Import SafetyDef.
Require Import UcoPreservation.

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section SafetyCriterion.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable T_evs S_evs : Events.
  Variable T_end S_end : Endstates.

  Local Definition trace__S := @trace S_evs S_end.
  Local Definition finpref__S := @finpref S_evs S_end.
  Local Definition trace__T := @trace T_evs T_end.
  Local Definition finpref__T := @finpref T_evs T_end.

  Local Definition prop__S := prop trace__S.
  Local Definition Safety__S := @Safety S_evs S_end.
  Local Definition prop__T := prop trace__T.
  Local Definition Safety__T := @Safety T_evs T_end.

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

  Local Definition Cl_τP := Cl_τP compilation_chain
                                 Source_Semantics Target_Semantics
                                 τ'.


  Local Definition σP := σP compilation_chain
                            Source_Semantics Target_Semantics
                            σ'.


  Definition rel_SC :=
    forall W (t : trace__T) (m : finpref__T),
      prefix m t ->  sem__T (W ↓) t ->
      (exists t' s, rel s t' /\ prefix m t' /\ sem__S W s).

  Theorem rel_SC_σSP : rel_SC <-> (forall W (π__T : prop__T), Safety__T π__T -> σP W π__T).
  Proof.
    have G2 : Galois_snd τ' σ' by firstorder.
    split.
    - move => Htilde W π HSafety. setoid_rewrite contra_σP.
      move => [t [Hsemt Hnot_t]].
      destruct (HSafety t Hnot_t) as [m [Hpref_m_t m_witness]].
      destruct (Htilde W t m) as [t' [s [Hrel_s_t' [Hpref_m_t' Hsem_s]]]]; auto.
      exists s. split; auto => Hσs.
      have Ht0 : π t'.
      { apply: G2; auto. now exists s. }
        by apply: (m_witness t').
    - move => H_RSP W t m Hpref_m_t Hsemt.
      have HSafetyπ : Safety__T (fun t' => ~ prefix m t').
      { move => t'. rewrite -dne => prefix_m_t'.
        now exists m. }
      move : (H_RSP W (fun t' => ~ prefix m t') HSafetyπ).
      setoid_rewrite contra_σP => Himp. destruct Himp as [s [Hsem_s Hσ]].
      now exists t.
      have : ~ (fun s': trace__S => s' = s) ⊆ (σ' (not ∘ prefix m)) by firstorder.
      rewrite -rel_adjunction_law not_forall_ex_not. move => [t' Ht'].
      move/not_imp: Ht' => [Ht' HHt'].
      exists t', s. repeat (split; auto).
      destruct Ht' as [s' [Heq Hs']]. by subst.
        by apply: NNPP.
  Qed.

  Theorem rel_SC_Cl_τTP : rel_SC <-> (forall W (π__S : prop__S), Cl_τP W π__S).
  Proof.
    setoid_rewrite <- (uco_adjuncts _ _ _ safety_uco rel_adjunction_law).
    by rewrite rel_SC_σSP -Safety_Cl_prop.
  Qed.

End SafetyCriterion.
