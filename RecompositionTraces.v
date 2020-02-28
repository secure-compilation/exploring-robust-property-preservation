
Require Import TraceModel.
Require Import CommonST.

Axiom src : language.

Definition semp (P:par src) (t : trace) := exists C, sem src (C[P]) t.
Definition semc (C:ctx src) (t : trace) := exists P, sem src (C[P]) t.

Definition trace_equiv P1 P2 := forall t, semp P1 t <-> semp P2 t.

Definition obs_equiv P1 P2 := forall C t, sem src (C[P1]) t <-> sem src (C[P2]) t.

Definition fats := forall P1 P2, trace_equiv P1 P2 <-> obs_equiv P1 P2.

(* In this model fats_rtl and decomposition are trivial *)

Lemma fats_rtl : forall P1 P2, obs_equiv P1 P2 -> trace_equiv P1 P2.
Proof.
  unfold obs_equiv, trace_equiv, semp. intros P1 P2 Hobs t.
  split; intros [C H].
  - rewrite -> Hobs in H. eauto.
  - rewrite <- Hobs in H. eauto.
Qed.

Lemma decomposition : forall C P t, sem src (C[P]) t -> (semp P t /\ semc C t).
Proof.
  unfold semp, semc. eauto.
Qed.

(* Composition is not trivial though *)

Definition composition := forall C P t, semp P t -> semc C t -> sem src (C[P]) t.

Lemma composition_trivial : composition.
Proof.
  unfold composition, semp, semc.
  intros C P m [C' H1] [P' H2].
Abort. (* what we are left with looks like recomposition *)

(* Composition follows from recomposition *)

Definition recomposition := forall C1 P1 C2 P2 t,
    sem src (C1[P1]) t -> sem src (C2[P2]) t -> sem src (C1[P2]) t.

Lemma recomposition_composition : recomposition -> composition.
Proof.
  unfold recomposition, composition, semp, semc.
  intros Hrecomp C P m [C' H1] [P' H2]. eapply Hrecomp; eassumption.
Qed.

(* Recomposition also follows from composition *)

Lemma composition_recomposition : composition -> recomposition.
Proof.
  unfold recomposition, composition, semp, semc.
  intros Hcomp C1 P1 C2 P2 t H0 H1.
  apply Hcomp; eexists; eassumption.
Qed.

(* FATs follows from recomposition *)

Lemma recomposition_fats : recomposition -> fats.
Proof.
  unfold recomposition, fats, trace_equiv, obs_equiv, semp.
  intros Hrecomp P1 P2. split; [| now apply fats_rtl].
  intros Htequiv C t. split; intro Hsem.
  - assert (H: exists C : ctx src, sem src (C [P1]) t) by eauto.
    rewrite -> Htequiv in H. destruct H as [C' H]. eapply Hrecomp; eassumption.
  - assert (H: exists C : ctx src, sem src (C [P2]) t) by eauto.
    rewrite <- Htequiv in H. destruct H as [C' H]. eapply Hrecomp; eassumption.
Qed.
