Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Criteria. 
Require Import ClassicalExtras.

Variable nd  : ctx src -> ctx src -> ctx src.

Infix "⊕" := nd (at level 50).  

Axiom nd_beh1 : forall C1 C2 P,
    forall t, beh (C1 [P]) t -> beh ((C1 ⊕ C2) [P]) t.  

Axiom nd_beh2 : forall C1 C2 P,
    forall t, beh (C2 [P]) t -> beh ((C1 ⊕ C2) [P]) t.

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

Lemma RSP_r2RSP : RSC -> r2RSC. 
Proof.
  rewrite RSC'. 
  intros rsc Ct P1 P2 m1 m2 H1 H2.
  destruct (rsc P1 Ct m1) as [Cs1 [t1 [Hpref1 Hs1]]]; auto.
  destruct (rsc P2 Ct m2) as [Cs2 [t2 [Hpref2 Hs2]]]; auto.
  exists (Cs1 ⊕ Cs2). unfold psem. split; [exists t1 | exists t2]; split; auto.   
  now apply nd_beh1. now apply nd_beh2.
Qed.

Lemma RTP_RSSCP : RC -> twoSCC. 
Proof.
  intros rc P Ct t1 t2 [Hsem1 Hsem2].
  destruct (rc P Ct t1) as [Cs1 H1]. specialize (H1 Hsem1). 
  destruct (rc P Ct t2) as [Cs2 H2]. specialize (H2 Hsem2).
  exists (Cs1 ⊕ Cs2). split; [apply nd_beh1 | apply nd_beh2]; auto.
Qed.


      