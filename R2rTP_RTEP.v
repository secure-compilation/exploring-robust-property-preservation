Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Criteria.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.
Require Import TechnicalLemmas.

(** This file proves that R2RTP implies RTEP *)


(** *our assumptions *)
(**********************************************************)
Hypothesis input_totality_tgt : @input_totality tgt.
Hypothesis determinacy_src    : @determinacy src.
Hypothesis tgt_sem            : @semantics_safety_like tgt.
(**********************************************************)


Theorem R2rTP_RTIP : R2rTP -> RTIP.
Proof.
  intros r2rpp. unfold RTIP. apply NNPP.
  intros hf. rewrite not_forall_ex_not in hf. destruct hf as [P1 hf].
  rewrite not_forall_ex_not in hf. destruct hf as [P2 hf].
  rewrite not_imp in hf. destruct hf as [H1 hf].
  unfold "⊆" in *.
  rewrite not_forall_ex_not in hf. destruct hf as [Ct hf].
  rewrite not_forall_ex_not in hf. destruct hf as [t hf].
  rewrite not_imp in hf. destruct hf as [k1 k2].
  specialize (r2rpp P1 P2 traces_match).
  assert (Hsat : rsat2 P1 P2 traces_match).
  { intros C b1 b2 Hb1 Hb2. apply (H1 C b1) in Hb1.
    unfold beh in Hb1.
    now apply (determinacy_src (C [P2])). }
  specialize (r2rpp Hsat Ct t); clear Hsat.
  assert (H : forall t2, sem tgt (Ct [P2 ↓]) t2 -> traces_match t t2).
  { intros t2 H. now apply r2rpp. } clear r2rpp H1.
  destruct (longest_in_psem tgt_sem (Ct [P2 ↓]) t k2) as [l [Hmt [Hpsem_m Hmax_m]]].
  destruct Hpsem_m as [t2 [Hmt2 Hsem_t2]].
  specialize (H t2 Hsem_t2). destruct H; try now subst.
  destruct H as [ll [i1 [i2 [Hi1 [Hi2 [Hdiffi [Hpref1 Hpref2]]]]]]].
  assert (psem (Ct [P2 ↓]) (ftbd (snoc ll i1))).
  { apply (input_totality_tgt (Ct [P2 ↓]) ll i2 i1); auto. now exists t2. }
  assert (fpr (ftbd (snoc ll i1)) l) by now apply Hmax_m.
  apply (fpr_pref_pref _ _ t2) in H0; auto.
  destruct (same_ext (ftbd (snoc ll i1)) (ftbd (snoc ll i2)) t2); auto;
    simpl in H1.
  ++ apply (list_snoc_pointwise ll ll i1 i2 i2 i2) in H1; auto.
     inversion H1. congruence. now apply list_list_prefix_ref.
  ++ apply (list_snoc_pointwise ll ll i2 i1 i1 i1) in H1; auto.
     inversion H1. congruence. now apply list_list_prefix_ref.
Qed.

Theorem R2rTP_RTEP : R2rTP -> RTEP.
Proof.  intros H. apply RTIP_RTEP. exact (R2rTP_RTIP H). Qed.
