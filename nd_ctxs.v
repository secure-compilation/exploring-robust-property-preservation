Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Criteria. 
Require Import ClassicalExtras.

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

Variable nd  : ctx src -> ctx src -> ctx src.

Infix "⊕" := nd (at level 50).


Axiom nd_beh1 : forall C1 C2 P, beh (C1 [P]) ⊆ beh ((C1 ⊕ C2) [P]).  

Axiom nd_beh2 : forall C1 C2 P, beh (C2 [P]) ⊆ beh ((C1 ⊕ C2) [P]).


(** *RSP -> R2rSP *)
(* and with a similar argument RSP -> R r_fin SP *)

Lemma RSC' : RSC <-> forall P Ct m, psem (Ct[P↓]) m -> exists Cs, psem (Cs[P]) m.
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

Lemma RTP_R2rTP : (forall P π, RP P π) -> r2RPP. 
Proof.
  rewrite <- RTC_RTP, r2RPP_r2RC.
  intros Hrc Ct P1 P2 t1 t2 H1 H2.
  destruct (Hrc P1 Ct t1) as [Cs1 Hs1]. specialize (Hs1 H1).
  destruct (Hrc P2 Ct t2) as [Cs2 Hs2]. specialize (Hs2 H2).
  exists (Cs1 ⊕ Cs2). split; [apply nd_beh1 | apply nd_beh2]; auto.
Qed.   

(** *RTP -> R2rTP *)
(* and with a similar argument RTP -> R r_fin TP *)


Lemma RSCCP_R2SSCP : ssc_cr -> (forall P1 P2 r, two_sc r -> ((hrsat2 P1 P2 r) -> hrsat2 (P1↓) (P2↓) r)).
Proof.
  rewrite two_scC. intros sscr P1 P2 Ct.
  destruct (sscr P1 Ct) as [Cs1 H1].
  destruct (sscr P2 Ct) as [Cs2 H2].
  exists (Cs1 ⊕ Cs2). split.
  + apply (subset_trans _ (beh (Cs1 [P1])) _).
    now unfold "⊆". apply nd_beh1.
  + apply (subset_trans _ (beh (Cs2 [P2])) _).
    now unfold "⊆". apply nd_beh2.
Qed.

Lemma RTP_R2SSCP : RTC ->  (forall P1 P2 r, two_sc r -> ((hrsat2 P1 P2 r) -> hrsat2 (P1↓) (P2↓) r)). 
Proof.
  rewrite two_scC. 
  intros rc P1 P2 Ct.
Abort.
(*we should apply rc for every t ∈ beh (ct[P1 ↓]) to get Cs_1 and 
                     for every t ∈ beh (ct[P2 ↓]) to get Cs_2, then 
  apply ⊕ and get the desired context. 
  When one of these two sets is infinite ⊕ should be applied infinitely many times

  Assuming finitary non determinism the implication can be proved.  

 *)

