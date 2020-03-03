
Require Import TraceModel.
Require Import CommonST.

Axiom src : language.

Definition psemp (P:par src) (m : finpref) := exists C, psem (C[P]) m.
Definition psemc (C:ctx src) (m : finpref) := exists P, psem (C[P]) m.

(* CH: Currently this defined only for finite trace prefixes, is that correct? *)
Definition trace_equiv P1 P2 := forall m, psemp P1 m <-> psemp P2 m.

(* CH: This is exactly how we defined the premise and conclusion of RTEP,
       yet usually FATs is more related to FA than to RTEP -- are we still
       convinced that the two agree in a determinate setting? [TOOD: read] *)
Definition obs_equiv P1 P2 := forall C t, sem src (C[P1]) t <-> sem src (C[P2]) t.

Definition fats := forall P1 P2, trace_equiv P1 P2 <-> obs_equiv P1 P2.

(* In this model fats_rtl and decomposition are trivial *)

(* CH: Isn't it already quite worrisome that one FATs direction holds no matter
       how informative or uninformative our traces are? *)

Lemma fats_rtl : forall P1 P2, obs_equiv P1 P2 -> trace_equiv P1 P2.
Proof.
  unfold obs_equiv, trace_equiv, psemp, psem. intros P1 P2 Hobs m.
  split; intros [C [t [Hpref Hpsem]]]; exists C, t.
  - rewrite -> Hobs in Hpsem. tauto.
  - rewrite <- Hobs in Hpsem. tauto.
Qed.

Lemma decomposition : forall C P m, psem (C[P]) m -> (psemp P m /\ psemc C m).
Proof.
  unfold psemp, psemc, psem. intros C P m [t [Hpref Hsem]]. split.
  - exists C, t. tauto.
  - exists P, t. tauto.
Qed.

(* Composition is not trivial though *)

Definition composition := forall C P m, psemp P m -> psemc C m -> psem (C[P]) m.
 
Lemma composition_trivial : composition.
Proof.
  unfold composition, psemp, psemc.
  intros C P m [C' H1] [P' H2].
Abort. (* what we are left with looks like recomposition *)

(* Composition follows from recomposition *)

Definition recomposition := forall C1 P1 C2 P2 m,
    @psem src (C1[P1]) m -> @psem src (C2[P2]) m -> @psem src (C1[P2]) m.

Lemma recomposition_composition : recomposition -> composition.
Proof.
  unfold recomposition, composition, psemp, psemc.
  intros Hrecomp C P m [C' H1] [P' H2]. eapply Hrecomp; eassumption.
Qed.

(* Recomposition also follows from composition *)

Lemma composition_recomposition : composition -> recomposition.
Proof.
  unfold recomposition, composition, psemp, psemc.
  intros Hcomp C1 P1 C2 P2 m H0 H1.
  apply Hcomp; eexists; eassumption.
Qed.

(* FATs follows from recomposition *)

Lemma recomposition_fats : recomposition -> fats.
Proof.
  unfold recomposition, fats, trace_equiv, obs_equiv, psemp, psem.
  intros Hrecomp P1 P2. split; [| now apply fats_rtl].
  intros Htequiv C t. split; intro Hsem.
Abort.

(* This is easier if we restrict obs_equiv to finite prefixes *)

Lemma recomposition_weak_fats : recomposition ->
  forall P1 P2, trace_equiv P1 P2 ->
  forall C m, psem (C[P1]) m <-> psem (C[P2]) m. (* <-- weaker obs_equiv *)
Proof.
  unfold recomposition, fats, trace_equiv, obs_equiv, psemp.
  intros Hrecomp P1 P2. intros H C m.
  split; intro Hsem.
  - assert (Hprem: exists C : ctx src, psem (C [P1]) m) by eauto.
    rewrite -> H in Hprem. destruct Hprem as [C' Hdone].
    eapply Hrecomp; eassumption.
  - assert (Hprem: exists C : ctx src, psem (C [P2]) m) by eauto.
    rewrite <- H in Hprem. destruct Hprem as [C' Hdone].
    eapply Hrecomp; eassumption.
Qed.

(* Now back to the more difficult proof, so let's go to classical logic *)

Require Import ClassicalExtras.

Module VeryStrongAssumption.
  (* Very strong assumption *)
  Axiom not_sem : forall C P t,
    ~sem src (C [P]) t -> exists m, prefix m t /\ ~psem (C[P]) m.

  Axiom exists_silent_div : exists C P, ~ sem src (C [P]) (tsilent nil). (* quite weak assumption *)

  Lemma false : False.
  Proof.
    pose proof exists_silent_div as [C [P H]].
    destruct (not_sem _ _ _ H) as [m [H1 H2]].
    assert (m = ftbd nil) by now destruct m as [|[]].
    subst.
    apply H2.
    destruct (non_empty_sem _ (C[P])) as [t Hsem].
    exists t; split; destruct t; now auto.
  Qed.

  (* CA: this is stronger than semantics_safety_like src and is equivalent to

     "H = forall W, forall t, (forall m ≤ t -> psem W m) -> sem W t".

     It is stronger than semantics_safety_like as t is arbitrary,
     and then H should also hold on silently diverging traces, that
     is not the case for semantics_safety_like.

     Assume sem W t for t being an infinite and non silently
     diverging trace, then psem W m for every m ≤ t.

     If we assume H, then sem W (silent m) for every m ≤ t, that
     means "W after producing every m can choose to silently diverge
     or to produce an other event e, such that m::e ≤ t" i.e. there
     is some internal non-determinism.  *)


  Lemma recomposition_fats : recomposition -> fats.
  Proof.
    (* unfold fats, trace_equiv, obs_equiv, psemp, psem. *)
    intros Hrecomp P1 P2. split; [| now apply fats_rtl].
    intros Htequiv. rewrite dne. intro Hc.
    do 2 setoid_rewrite not_forall_ex_not in Hc.
    destruct Hc as [C [t Hc]]. rewrite not_iff in Hc.
    destruct Hc as [[H1 H2] | [H2 H1]].
    - apply not_sem in H2. destruct H2 as [m [Hpref H2]]. apply H2. clear H2.
      rewrite <- recomposition_weak_fats;
        [ exists t; now eauto | assumption | assumption ].
    - apply not_sem in H2. destruct H2 as [m [Hpref H2]]. apply H2. clear H2.
      rewrite -> recomposition_weak_fats;
        [ exists t; now eauto | assumption | assumption ].
  Qed.

End VeryStrongAssumption.
