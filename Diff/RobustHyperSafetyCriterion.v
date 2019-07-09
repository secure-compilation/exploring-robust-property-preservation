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
Require Import RobustHyperSafetyPreservation.
Require Import RobustSSCHCriterion.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section RobustHSafeCriterion.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable T_evs S_evs : Events.
  Variable T_end S_end : Endstates.

  Local Definition trace__S := @trace S_evs S_end.
  Local Definition finpref__S := @finpref S_evs S_end.
  Local Definition trace__T := @trace T_evs T_end.
  Local Definition finpref__T := @finpref T_evs T_end.
  Local Definition prefix__T := @prefix T_evs T_end.

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

  Variable rel : trace__S -> trace__T -> Prop.

  Local Definition adjunction :=  induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.

  Local Definition sCl_σRhP := sCl_σRhP compilation_chain
                                        Source_Semantics Target_Semantics
                                        σ'.

  Local Definition hsCl_τRhP := hsCl_τRhP compilation_chain
                                          Source_Semantics Target_Semantics
                                          τ'.

  Definition rel_RHSC :=
    forall P C__T (M : finpref -> Prop), Observations M ->
       M <<< (beh__T (plug__T (P↓) C__T)) ->
       (exists C__S, forall m, M m -> exists t s, prefix__T m t /\
                                    rel s t /\
                                    beh__S (plug__S P C__S) s).

  Lemma conclusion_RSHC (P : par__S) (M : finpref__T -> Prop) (C__S : ctx__S) :
    (forall m, M m -> exists t s, prefix__T m t /\
                          rel s t /\
                          beh__S (plug__S P C__S) s) <->
    M <<< τ' (beh__S (plug__S P C__S)).
  Proof. firstorder. Qed.

  Local Definition rel_RSCHC := @rel_RSCHC Source Target compilation_chain trace__S trace__T
                                           Source_Semantics Target_Semantics rel.


  Lemma rel_RSCHC_rel_RHSC : rel_RSCHC -> rel_RHSC.
  Proof.
    move => H_tilde P Ct M Obs_M H_M.
    destruct (H_tilde P Ct) as [Cs H_Cs].
    exists Cs => m M_m.
    destruct (H_M m M_m) as [t [H_t m_pref_t]].
    destruct (H_Cs t H_t) as [s [rel_s_t H_s]]. now exists t, s.
  Qed.

  Theorem rel_RHSC_sCl_σRHSP :
    rel_RHSC <-> (forall P (H: hprop__T), HSafe H ->  sCl_σRhP P H).
  Proof.
    split.
    - move => H_tilde P H__T H_HSafe.
      setoid_rewrite contra_σRhP. move => [Ct H_tgt].
      destruct (H_HSafe _ H_tgt) as  [M [M_obs [M_leq_beh M_wit]]].
      destruct (H_tilde P Ct M) as [Cs H_conclusion]; auto.
      move/conclusion_RSHC : H_conclusion => H_conclusion.
      exists Cs => Hf. destruct Hf as [bs [H_bs beh_γ_bs]].
      destruct H_bs as [bt [H_bt Heq]]. subst.
      move/rel_adjunction_law : beh_γ_bs => τ_beh_bt.
      apply: (M_wit bt); auto.
      { move => m M_m. destruct (H_conclusion m) as [t [H_t pref_m_t]]; auto.
        exists t. split; auto. }
    - move => Hσ P Ct M M_obs M_leq_beh_tgt.
      have HSafe_H : HSafe (fun b :prop__T => ~ M <<< b).
      { move => b. rewrite -dne => M_b. now exists M. }
      move/contra: (Hσ P (fun b : prop__T => ~ M <<< b) HSafe_H).
      rewrite !neg_rhsat. move => HγP.
      destruct HγP as [Cs H_src]. by exists Ct.
      exists Cs. rewrite conclusion_RSHC.
      apply: NNPP => Hf. apply: H_src.
      exists (σ' (τ' (beh__S (plug__S P Cs)))). split.
      + by exists (τ' (beh__S (plug__S P Cs))).
      +  move/Galois_equiv : rel_adjunction_law.
         move => [mono_gamma [mono_tau [G1 G2]]]. by apply: G1.
  Qed.

   Theorem rel_RHSC_hsCl_τRHSP :
    rel_RHSC <-> (forall P (H: hprop__S), SSC H ->  hsCl_τRhP P H).
   Proof.
     setoid_rewrite <- τRSCHP_σRSCHP.
     exact rel_RHSC_sCl_σRHSP.
     exact rel_adjunction_law.
   Qed.

End RobustHSafeCriterion.