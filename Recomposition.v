
Require Import TraceModel.
Require Import CommonST.

Axiom src : language.

(* Defining partial semantics for programs and contexts in terms of the
   whole-program semantics; here we only look at finite prefixes as we currently
   do in our CCS'18 recomposition proof *)
(* CH: An important assumption here is that the whole-program traces already
       include enough information to define a "proper" partial-program semantics
   CH: This might be related to our previous conjecture that adding the
       information needed to achieve "FATs" to the trace does not prevent any
       extra optimizations?
   CH: And anyway, composition / recomposition / FATs(?) should be strong
       enough conditions to enforce this assumption? So "proper" above could
       well mean satisfying composition / recomposition / FATs *)
Definition psemp (P:par src) (m : finpref) := exists C, psem (C[P]) m.
Definition psemc (C:ctx src) (m : finpref) := exists P, psem (C[P]) m.

(* Trace equivalence defined over partial semantics and only for
   finite trace prefixes, as usually the case in the literature *)
Definition trace_equiv P1 P2 := forall m, psemp P1 m <-> psemp P2 m.

(* CH: This is exactly how we defined the premise and conclusion of RTEP,
       yet usually FATs is more related to FA than to RTEP -- are we still
       convinced that the two agree in a determinate setting? [TOOD: read] *)
(* CH: After 2020-03-10 discussion, this definition has little to do with
       observational equivalence, which means that the thing below should not
       be called FATs either *)
Definition beh_equiv P1 P2 := forall C t, sem src (C[P1]) t <-> sem src (C[P2]) t.

Definition not_really_fats := forall P1 P2, trace_equiv P1 P2 <-> beh_equiv P1 P2.

(* In this model not_really_fats_rtl and decomposition are trivial *)
(* CH: Isn't the former already quite worrisome that one FATs direction holds no
       matter how informative or uninformative our traces are? Not if the above
       is not really FATs though ... *)

Lemma beh_equiv_trace_equiv : forall P1 P2, beh_equiv P1 P2 -> trace_equiv P1 P2.
Proof.
  unfold beh_equiv, trace_equiv, psemp, psem. intros P1 P2 Hbe m.
  split; intros [C [t [Hpref Hpsem]]]; exists C, t.
  - rewrite -> Hbe in Hpsem. tauto.
  - rewrite <- Hbe in Hpsem. tauto.
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

(* not_really_fats follows from recomposition *)

Lemma recomposition_fats : recomposition -> not_really_fats.
Proof.
  unfold recomposition, not_really_fats, trace_equiv, beh_equiv, psemp, psem.
  intros Hrecomp P1 P2. split; [| now apply beh_equiv_trace_equiv].
  intros Htequiv C t. split; intro Hsem.
Abort.

(* This is easier if we restrict beh_equiv to finite prefixes *)

Lemma recomposition_trace_equiv_weak_beh_equiv : recomposition ->
  forall P1 P2, trace_equiv P1 P2 ->
  forall C m, psem (C[P1]) m <-> psem (C[P2]) m. (* <-- weaker beh_equiv *)
Proof.
  unfold recomposition, trace_equiv, psemp.
  intros Hrecomp P1 P2. intros H C m.
  split; intro Hsem.
  - assert (Hprem: exists C : ctx src, psem (C [P1]) m) by eauto.
    rewrite -> H in Hprem. destruct Hprem as [C' Hdone].
    eapply Hrecomp; eassumption.
  - assert (Hprem: exists C : ctx src, psem (C [P2]) m) by eauto.
    rewrite <- H in Hprem. destruct Hprem as [C' Hdone].
    eapply Hrecomp; eassumption.
Qed.

(* Now back to the more difficult proof (and broken), so let's go to classical logic *)

Require Import ClassicalExtras.

Module VeryStrongAssumption.
  (* Too strong assumption made silently in Deepak's proof
     - Jeremy proved false from it below
       (using the presence of silent divergence in the traces) *)
  Axiom not_sem : forall C P t,
    ~sem src (C [P]) t -> exists m, prefix m t /\ ~psem (C[P]) m.

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

  Axiom exists_silent_div : exists C P, ~ sem src (C [P]) (tsilent nil). (* weak assumption *)

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

  Lemma recomposition_not_really_fats : recomposition -> not_really_fats.
  Proof.
    (* unfold fats, trace_equiv, obs_equiv, psemp, psem. *)
    intros Hrecomp P1 P2. split; [| now apply beh_equiv_trace_equiv].
    intros Htequiv. rewrite dne. intro Hc.
    do 2 setoid_rewrite not_forall_ex_not in Hc.
    destruct Hc as [C [t Hc]]. rewrite not_iff in Hc.
    destruct Hc as [[H1 H2] | [H2 H1]].
    - apply not_sem in H2. destruct H2 as [m [Hpref H2]]. apply H2. clear H2.
      rewrite <- recomposition_trace_equiv_weak_beh_equiv;
        [ exists t; now eauto | assumption | assumption ].
    - apply not_sem in H2. destruct H2 as [m [Hpref H2]]. apply H2. clear H2.
      rewrite -> recomposition_trace_equiv_weak_beh_equiv;
        [ exists t; now eauto | assumption | assumption ].
  Qed.

End VeryStrongAssumption.

Module WeakerAssumption.
  (* should follow from `semantics_safety_like src` *)
  Axiom not_sem : forall C P t,
    ~sem src (C [P]) t -> ~diverges t -> exists m, prefix m t /\ ~psem (C[P]) m.

  Lemma recomposition_not_really_fats : recomposition -> not_really_fats.
  Proof.
    intros Hrecomp P1 P2. split; [| now apply beh_equiv_trace_equiv].
    intros Htequiv. intros C t.
    destruct t as [ m es | m | s ].
    - eapply (recomposition_trace_equiv_weak_beh_equiv Hrecomp)
        with (m := fstop m es) (C := C) in Htequiv. unfold psem in Htequiv.
      (* the rest is just a lot of boilerplate to prove something obvious *)
      destruct Htequiv as [Htequiv1 Htequiv2]. split; intro H.
      + assert (H' : exists t, prefix (fstop m es) t /\ sem src (C [P1]) t).
          { exists (tstop m es). simpl. tauto. }
        destruct (Htequiv1 H') as [t' [Hprefix Hsem]]. destruct t'; simpl in Hprefix.
        * destruct Hprefix as [H1 H2]. subst. assumption.
        * contradiction.
        * contradiction.
      + assert (H' : exists t, prefix (fstop m es) t /\ sem src (C [P2]) t).
          { exists (tstop m es). simpl. tauto. }
        destruct (Htequiv2 H') as [t' [Hprefix Hsem]]. destruct t'; simpl in Hprefix.
        * destruct Hprefix as [H1 H2]. subst. assumption.
        * contradiction.
        * contradiction.
    - unfold trace_equiv, psemp, psem in Htequiv. specialize (Htequiv (ftbd m)).
      admit. (* <-- this case doesn't work *)
    - rewrite dne. intro Hc. rewrite not_iff in Hc.
      destruct Hc as [[H1 H2] | [H2 H1]].
      + apply not_sem in H2. simpl in H2. destruct H2 as [m [Hpref H2]]. apply H2. clear H2.
        rewrite <- recomposition_trace_equiv_weak_beh_equiv;
          [ exists (tstream s); now eauto | assumption | assumption ]. tauto.
      + apply not_sem in H2. destruct H2 as [m [Hpref H2]]. apply H2. clear H2.
        rewrite -> recomposition_trace_equiv_weak_beh_equiv;
          [ exists (tstream s); now eauto | assumption | assumption ]. tauto.
  Abort.

End WeakerAssumption.
