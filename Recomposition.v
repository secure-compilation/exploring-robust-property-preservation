
Require Import TraceModel.
Require Import CommonST.

Axiom src : language.

Definition psemp (P:par src) (m : finpref) := exists C, psem (C[P]) m.
Definition psemc (C:ctx src) (m : finpref) := exists P, psem (C[P]) m.

Definition trace_equiv P1 P2 := forall m, psemp P1 m <-> psemp P2 m.

Definition obs_equiv P1 P2 := forall C t, sem src (C[P1]) t <-> sem src (C[P2]) t.

Definition fats := forall P1 P2, trace_equiv P1 P2 <-> obs_equiv P1 P2.

(* In this model fats_rtl and decomposition are trivial *)

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

(* Recomposition follows from composition *)

Lemma composition_recomposition : composition -> recomposition.
Proof.
  unfold recomposition, composition, psemp, psemc.
  intros Hcomp C1 P1 C2 P2 m H0 H1.
  apply Hcomp; eexists; eassumption.
Qed.

(* FATs follows from recomposition *)

Lemma recomposition_fats : recomposition -> fats.
Proof.
  unfold recomposition, fats, trace_equiv, obs_equiv.
  intros Hrecomp P1 P2. split; [| now apply fats_rtl]. intros Htequiv C t.
  split; intro Hsem.
Admitted.
