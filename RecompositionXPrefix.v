
Require Import TraceModel.
Require Import CommonST.
Require Import XPrefix.

Axiom src : language.

(* Generically defining partial/trace (big-step) semantics for programs (xsemp)
   and contexts (xsemc) in terms of the whole-program (big-step) semantics
   (xsem); here we only look at finitely representable prefixes, a small
   extension over what we currently do in our CCS'18 recomposition proof.

   One big difference wrt our previous composition/decomposition proofs, is that
   we are looking only at big-step semantics, while at at CCS'18 we were
   originally defining partial small-step(!) semantics that were
   nondeterministically changing the context in every step, which was a huge
   pain to work with.

   An important assumption here is that the whole-program traces already include
   enough information to define a "proper" partial-program semantics This seems
   in part related to our 2nd conjecture that adding the information needed to
   achieve FATs to the trace does not prevent any extra optimizations?  And
   anyway, composition / recomposition / [det-]FATs should be strong enough
   conditions to enforce this assumption? So "proper" above could well mean
   satisfying composition / recomposition / [det-]FATs. *)

Definition xsemp (P:par src) (m : xpref) := exists C, xsem (C[P]) m.
Definition xsemc (C:ctx src) (m : xpref) := exists P, xsem (C[P]) m.

(* Trace equivalence defined over partial semantics and only for finitely
   representable trace prefixes.

   CH: TODO: still unclear to me whether in the literature they explicitly mark
             silent divergence as a final event in these prefixes. *)

Definition trace_equiv P1 P2 := forall m, xsemp P1 m <-> xsemp P2 m.

(* As a the "golden equivalence" we use beh_equiv, which corresponds exactly to
   the premise and conclusion of RTEP (which should really be called RBEP).

   In the determinate setting this definition seems fine to use as the "golden
   equivalence" in FATs, but with internal nondeterminism we would instead need
   to use some barbed bisimulation, which is defined coinductively and is very
   specific to the language at hand, thus hardly suited for this kind of
   language-generic generic proofs.

   So for now let's assume a determinate setting, even if the precise role of
   determinacy in making beh_equiv suitable is still to be formally investigated
   (we are not in the same setting as Engelfriet [TCS, 1985] for instance).

   Here t does capture the internal interaction between C and P1/P2, but
   that's not always standard. *)

Definition beh_equiv P1 P2 := forall C t, sem src (C[P1]) t <-> sem src (C[P2]) t.

Definition det_fats := forall P1 P2, trace_equiv P1 P2 <-> beh_equiv P1 P2.

(* In this model det_fats_rtl (completeness) and decomposition are trivial *)
(* The fact that the completeness direction of FATs holds unconditionally
   is a specificity of our setup (i.e. the way we defined xsemp) *)

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

(* Composition is not trivial, but equivalent to recomposition *)

Definition composition := forall C P m, xsemp P m -> xsemc C m -> xsem (C[P]) m.

Lemma composition_not_trivial : composition.
Proof.
  unfold composition, xsemp, xsemc.
  intros C P m [C' H1] [P' H2].
Abort. (* what we are left with looks like recomposition *)

(* Composition follows from recomposition *)
(* This definition of recomposition is a slight generalization of the CCS'18 one.
   This bakes in a few things:
   - we are only looking at finitely representable prefixes
     (artifact of looking at RXP or RFrXP for back-translation reasons)
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

(* Our conjecture: det_fats follows from recomposition *)

Lemma recomposition_det_fats : recomposition -> det_fats.
Proof.
  unfold recomposition, det_fats, trace_equiv, beh_equiv, xsemp, xsem.
  intros Hrecomp P1 P2. split; [| now apply beh_equiv_trace_equiv].
  intros Htequiv C t. split; intro Hsem.
Abort.

(* This is easier if we first restrict beh_equiv to finitely representable
   prefixes. This is used in the more general theorem below. *)

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

(* Now back to the more difficult proof, so let's go to classical logic *)

Require Import ClassicalExtras.

Module NewAssumption.
  (* Assumption made silently in Deepak's proof *)
  (* should follow from `semantics_safety_like src`, right? *)
  Axiom not_sem : forall C P t,
    ~sem src (C [P]) t -> exists m, xprefix m t /\ ~xsem (C[P]) m.

  Theorem recomposition_det_fats : recomposition -> det_fats.
  Proof.
    (* unfold fats, trace_equiv, obs_equiv, xsemp, xsem. *)
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
