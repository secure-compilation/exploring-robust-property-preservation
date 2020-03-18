
Require Import TraceModel.
Require Import CommonST.
Require Import XPrefix.

Axiom src : language.

(* Defining partial/trace semantics for programs and contexts in terms of the
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
Definition xsemp (P:par src) (m : xpref) := exists C, xsem (C[P]) m.
Definition xsemc (C:ctx src) (m : xpref) := exists P, xsem (C[P]) m.

(* Trace equivalence defined over partial semantics and only for
   finite trace prefixes, as usually the case in the literature *)
Definition trace_equiv P1 P2 := forall m, xsemp P1 m <-> xsemp P2 m.

(* CH: This is exactly how we defined the premise and conclusion of RTEP,
       yet usually FATs is more related to FA than to RTEP -- are we still
       convinced that the two agree in a determinate setting? [TOOD: read] *)
(* CH: After 2020-03-10 discussion, this definition has little to do with
       observational equivalence, which means that the thing below should not
       be called FATs either -- in particular this definition is not the right
       one for FATs in the presence of internal nondeterminism *)
Definition beh_equiv P1 P2 := forall C t, sem src (C[P1]) t <-> sem src (C[P2]) t.

Definition not_really_fats := forall P1 P2, trace_equiv P1 P2 <-> beh_equiv P1 P2.

(* In this model not_really_fats_rtl and decomposition are trivial *)
(* CH: Isn't the former already quite worrisome that one FATs direction holds no
       matter how informative or uninformative our traces are? Not if the above
       is not really FATs though ... *)

Lemma beh_equiv_trace_equiv : forall P1 P2, beh_equiv P1 P2 -> trace_equiv P1 P2.
Proof.
  unfold beh_equiv, trace_equiv, xsemp, xsem. intros P1 P2 Hbe m.
  split; intros [C [t [Hpref Hpsem]]]; exists C, t.
  - rewrite -> Hbe in Hpsem. tauto.
  - rewrite <- Hbe in Hpsem. tauto.
Qed.

Lemma decomposition : forall C P m, xsem (C[P]) m -> (xsemp P m /\ xsemc C m).
Proof.
  unfold xsemp, xsemc, xsem. intros C P m [t [Hpref Hsem]]. split.
  - exists C, t. tauto.
  - exists P, t. tauto.
Qed.

(* Composition is not trivial though *)

Definition composition := forall C P m, xsemp P m -> xsemc C m -> xsem (C[P]) m.

Lemma composition_trivial : composition.
Proof.
  unfold composition, xsemp, xsemc.
  intros C P m [C' H1] [P' H2].
Abort. (* what we are left with looks like recomposition *)

(* Composition follows from recomposition *)
(* This definition matches the CCS'18 one. This bakes in a few things:
   - we are only looking at prefixes (artifact of just looking at RSC)
   - whole-program semantics defined in terms of traces (prefixes) of events,
     which for us are pretty informative (this definition is agnostic to that) *)
Definition recomposition := forall C1 P1 C2 P2 m,
    @xsem src (C1[P1]) m -> @xsem src (C2[P2]) m -> @xsem src (C1[P2]) m.

Lemma recomposition_composition : recomposition -> composition.
Proof.
  unfold recomposition, composition, xsemp, xsemc.
  intros Hrecomp C P m [C' H1] [P' H2]. eapply Hrecomp; eassumption.
Qed.

(* Recomposition also follows from composition *)

Lemma composition_recomposition : composition -> recomposition.
Proof.
  unfold recomposition, composition, xsemp, xsemc.
  intros Hcomp C1 P1 C2 P2 m H0 H1.
  apply Hcomp; eexists; eassumption.
Qed.

(* Our original conjecture: not_really_fats follows from recomposition *)

Lemma recomposition_not_really_fats : recomposition -> not_really_fats.
Proof.
  unfold recomposition, not_really_fats, trace_equiv, beh_equiv, xsemp, xsem.
  intros Hrecomp P1 P2. split; [| now apply beh_equiv_trace_equiv].
  intros Htequiv C t. split; intro Hsem.
Abort.

(* This is easier if we restrict beh_equiv to finitely representable prefixes *)

Lemma recomposition_trace_equiv_weak_beh_equiv : recomposition ->
  forall P1 P2, trace_equiv P1 P2 ->
  forall C m, xsem (C[P1]) m <-> xsem (C[P2]) m. (* <-- weaker beh_equiv *)
Proof.
  unfold recomposition, trace_equiv, xsemp.
  intros Hrecomp P1 P2. intros H C m.
  split; intro Hsem.
  - assert (Hprem: exists C : ctx src, xsem (C [P1]) m) by eauto.
    rewrite -> H in Hprem. destruct Hprem as [C' Hdone].
    eapply Hrecomp; eassumption.
  - assert (Hprem: exists C : ctx src, xsem (C [P2]) m) by eauto.
    rewrite <- H in Hprem. destruct Hprem as [C' Hdone].
    eapply Hrecomp; eassumption.
Qed.

(* Now back to the more difficult proof (and broken), so let's go to classical logic *)

Require Import ClassicalExtras.

Module NewAssumption.
  (* Assumption made silently in Deepak's proof *)
  (* should follow from `semantics_safety_like src` ? *)
  Axiom not_sem : forall C P t,
    ~sem src (C [P]) t -> exists m, xprefix m t /\ ~xsem (C[P]) m.

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

End NewAssumption.
