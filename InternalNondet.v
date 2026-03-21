Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Criteria.
Require Import ClassicalExtras.
From Stdlib Require Import List.

(** This file proves the collapses that happens in presence of
    a non-deterministic choice operator in the source language *)


(*

   RrHP ------
               \
    |          RrSCP----
               /          \
   RFrHP      /           RrTP ----
             /            /        \
    |       /            /          \
           /            /           RrSP
   RHP--- /            /             |
         /            /              |
    |   /            /               |
       /            /                |
   RSCP  --------- /                 |
                  /-                 |
    |            /                   /
          -----                     /
   RTP (<-> RFrTP)                 /
                                  /
                                 /
   / \                          /
                               /
 RDP  RSP (<-> RFrSP) ---------

*)

(** ** We start with a binary non-deterministic choice operator on contexts *)

Axiom nd  : ctx src i -> ctx src i -> ctx src i.

Infix "⊕" := nd (at level 50).


Axiom nd_beh1 : forall C1 C2 P, beh (C1 [P]) ⊆ beh ((C1 ⊕ C2) [P]).

Axiom nd_beh2 : forall C1 C2 P, beh (C2 [P]) ⊆ beh ((C1 ⊕ C2) [P]).


(** *RSP -> R2rSP *)
(* and with a similar argument RSP -> R r_fin SP *)

Lemma RSC' : RSC <-> forall (P : par src i) Ct m, psem (Ct[P↓]) m -> exists Cs, psem (Cs[P]) m.
Proof.
  split.
  + intros rsc P Ct m [t [Hpref Hsem]].
    destruct (rsc P Ct t Hsem m Hpref) as [Cs [t' [Hsem' Hpref']]].
    exists Cs. now exists t'.
                + intros rsc' P Ct t Hsem m Hpref.
                  destruct (rsc' P Ct m) as  [Cs [t' [Hpref' Hsem']]].
                  now exists t.
                        now exists Cs, t'.
Qed.

Lemma RSP_R2rSP : RSC -> R2rSC.
Proof.
  rewrite RSC'.
  intros rsc Ct P1 P2 m1 m2 H1 H2.
  destruct (rsc P1 Ct m1) as [Cs1 [t1 [Hpref1 Hs1]]]; auto.
  destruct (rsc P2 Ct m2) as [Cs2 [t2 [Hpref2 Hs2]]]; auto.
  exists (Cs1 ⊕ Cs2). unfold psem. split; [exists t1 | exists t2]; split; auto.
  now apply nd_beh1. now apply nd_beh2.
Qed.


(** *RTP -> R2rTP *)
(* and with a similar argument RTP -> R r_fin TP *)

Lemma RTP_R2rTP : RTP -> R2rTP.
Proof.
  rewrite <- RTC_RTP, <- R2rTC_R2rTP.
  intros Hrc Ct P1 P2 t1 t2 H1 H2.
  destruct (Hrc P1 Ct t1) as [Cs1 Hs1]. specialize (Hs1 H1).
  destruct (Hrc P2 Ct t2) as [Cs2 Hs2]. specialize (Hs2 H2).
  exists (Cs1 ⊕ Cs2). split; [apply nd_beh1 | apply nd_beh2]; auto.
Qed.

(** *RTP -> R2rTP *)
(* and with a similar argument RTP -> R r_fin TP *)


Lemma RSCHP_R2rSCHP : RSCHP -> R2rSCHP.
Proof.
  rewrite <- R2rSCHC_R2rSCHP, <- RSCHC_RSCHP. intros sscr P1 P2 Ct.
  destruct (sscr P1 Ct) as [Cs1 H1].
  destruct (sscr P2 Ct) as [Cs2 H2].
  exists (Cs1 ⊕ Cs2). split.
  + apply (subset_trans _ (beh (Cs1 [P1])) _).
    now unfold "⊆". apply nd_beh1.
  + apply (subset_trans _ (beh (Cs2 [P2])) _).
    now unfold "⊆". apply nd_beh2.
Qed.


(** ** More collapses when some of the sets are finite *)

(** When each target program produces finitely many traces,
    ⊕ can be applied finitely many times to collapse RTC to RSCHC,
    and then to R2rSCHP. *)

Axiom finite_trace_sets_tgt : forall (W : prg tgt),
  exists (l : list trace), forall t, sem tgt W t <-> In t l.

(** Helper: given a finite list of traces, each covered by some source
    context, we can join them all with ⊕ into a single context. *)
Lemma nd_cover_list : forall (P : par src i) (default : ctx src i) (l : list trace),
  (forall t, In t l -> exists Cs, sem src (Cs [P]) t) ->
  exists Cs, forall t, In t l -> sem src (Cs [P]) t.
Proof.
  intros P default l. induction l as [| t0 l' IH].
  - intros _. exists default. intros t [].
  - intros H.
    destruct (H t0 (or_introl eq_refl)) as [Cs0 HCs0].
    assert (Hl' : forall t, In t l' -> exists Cs, sem src (Cs [P]) t).
    { intros t Hin. apply H. right. exact Hin. }
    destruct (IH Hl') as [Cs_rest HCs_rest].
    exists (Cs0 ⊕ Cs_rest).
    intros t [Heq | Hin].
    + subst. apply (nd_beh1 Cs0 Cs_rest P). exact HCs0.
    + apply (nd_beh2 Cs0 Cs_rest P). exact (HCs_rest t Hin).
Qed.

(** Key step: RTC gives a source context per trace; we join finitely
    many of them into one context that covers all traces of a given
    program. *)
Lemma RTC_RSCHC : RTC -> RSCHC.
Proof.
  intros rtc P C'.
  destruct (finite_trace_sets_tgt (C' [P↓])) as [l Hl].
  (* Get a default source context (needed for empty list base case) *)
  destruct (rtc P C' (tsilent nil)) as [default _].
  (* For each trace in l, RTC gives a source context *)
  assert (Hcover : forall t, In t l -> exists Cs, sem src (Cs [P]) t).
  { intros t Hin. destruct (rtc P C' t) as [Cs HCs].
    exists Cs. apply HCs. apply Hl. exact Hin. }
  destruct (nd_cover_list P default l Hcover) as [Cs HCs].
  exists Cs. intros t Ht. apply HCs. apply Hl. exact Ht.
Qed.

(** Combined: RTC -> R2rSCHP (= R2rSCHC).
    Previously blocked because ⊕ needed to be applied infinitely
    many times; finite trace sets make it finite. *)
Lemma RTC_R2rSCHP : RTC -> R2rSCHP.
Proof.
  intro Hrtc. apply RSCHP_R2rSCHP. rewrite <- RSCHC_RSCHP.
  exact (RTC_RSCHC Hrtc).
Qed.

(** Finitely many source partial programs (nonempty).
    Together with finite trace sets and ⊕, this collapses
    RTC all the way to RrSCHC. *)
Axiom finite_program_set_src : exists (P0 : par src i) (l : list (par src i)),
  forall P, In P (P0 :: l).

(** Helper: joining RSCHC witnesses over a finite list of programs. *)
Lemma nd_cover_programs : forall (Ct : ctx tgt (cint i)) (default : ctx src i)
  (l : list (par src i)),
  (forall P, In P l -> exists Cs, forall t, sem tgt (Ct [P↓]) t -> sem src (Cs [P]) t) ->
  exists Cs, forall P, In P l -> forall t, sem tgt (Ct [P↓]) t -> sem src (Cs [P]) t.
Proof.
  intros Ct default l. induction l as [| P0 l' IH].
  - intros _. exists default. intros P [].
  - intros H.
    destruct (H P0 (or_introl eq_refl)) as [Cs0 HCs0].
    destruct (IH (fun P Hin => H P (or_intror Hin))) as [Cs_rest HCs_rest].
    exists (Cs0 ⊕ Cs_rest).
    intros P [Heq | Hin] t Ht.
    + subst. apply (nd_beh1 Cs0 Cs_rest P). apply HCs0. exact Ht.
    + apply (nd_beh2 Cs0 Cs_rest P). apply (HCs_rest P Hin). exact Ht.
Qed.

(** With ⊕ and finitely many programs, RSCHC implies RrSCHC:
    join per-program witnesses into a single context for all programs. *)
Lemma RSCHC_RrSCHC : RSCHC -> RrSCHC.
Proof.
  intros rschc Ct.
  destruct finite_program_set_src as [P0 [progs Hprogs]].
  (* Get a default source context from RSCHC applied to P0 *)
  destruct (rschc P0 Ct) as [default _].
  destruct (nd_cover_programs Ct default (P0 :: progs)) as [Cs HCs].
  { intros P _. exact (rschc P Ct). }
  exists Cs. unfold beh, "⊆". intros P t Ht.
  exact (HCs P (Hprogs P) t Ht).
Qed.

(** Full collapse: RTC -> RrSCHC (= RrSCHP).
    Uses finitary target ND (for traces) and finitary programs. *)
Lemma RTC_RrSCHC : RTC -> RrSCHC.
Proof.
  intro Hrtc. apply RSCHC_RrSCHC. exact (RTC_RSCHC Hrtc).
Qed.


(** ** Same collapses with infinitary non-deterministic choice.

    With an infinitary join on source contexts, the same collapses
    hold without any finiteness assumptions (no finite_trace_sets_tgt,
    no finite_program_set_src). The predicate-indexed formulation also
    avoids the axiom of choice. *)

Axiom nd_inf : (ctx src i -> Prop) -> ctx src i.

Axiom nd_inf_beh : forall (F : ctx src i -> Prop) C P,
  F C -> beh (C [P]) ⊆ beh (nd_inf F [P]).

Lemma RTC_RSCHC_inf : RTC -> RSCHC.
Proof.
  intros rtc P Ct.
  (* F collects all source contexts that correctly simulate some target trace *)
  set (F := fun C => exists t, sem tgt (Ct [P↓]) t /\ sem src (C [P]) t).
  exists (nd_inf F). intros t Ht.
  destruct (rtc P Ct t) as [Cs HCs]. specialize (HCs Ht).
  apply (nd_inf_beh F Cs P).
  - exists t. auto.
  - exact HCs.
Qed.

Lemma RSCHC_RrSCHC_inf : RSCHC -> RrSCHC.
Proof.
  intros rschc Ct.
  (* F collects all source contexts that simulate some program *)
  set (F := fun C => exists P, forall t, sem tgt (Ct [P↓]) t -> sem src (C [P]) t).
  exists (nd_inf F). unfold beh, "⊆". intros P t Ht.
  destruct (rschc P Ct) as [Cs HCs].
  apply (nd_inf_beh F Cs P).
  - exists P. exact HCs.
  - exact (HCs t Ht).
Qed.

Lemma RTC_RrSCHC_inf : RTC -> RrSCHC.
Proof.
  intro Hrtc. apply RSCHC_RrSCHC_inf. exact (RTC_RSCHC_inf Hrtc).
Qed.
