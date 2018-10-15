Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Criteria. 
Require Import ClassicalExtras.

Variable nd  : ctx src -> ctx src -> ctx src.

Infix "⊕" := nd (at level 50).
Infix "⊆" := subset (at level 50). 

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

Lemma RSP_r2RSP : RSC -> r2RSC. 
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

Lemma RTP_r2RTP : (forall P π, RP P π) -> r2RPP. 
Proof.
  rewrite <- RC_RPP, r2RPP_r2RC.
  intros Hrc Ct P1 P2 t1 t2 H1 H2.
  destruct (Hrc P1 Ct t1) as [Cs1 Hs1]. specialize (Hs1 H1).
  destruct (Hrc P2 Ct t2) as [Cs2 Hs2]. specialize (Hs2 H2).
  exists (Cs1 ⊕ Cs2). split; [apply nd_beh1 | apply nd_beh2]; auto.
Qed.   

(** *RTP -> R2rTP *)
(* and with a similar argument RTP -> R r_fin TP *)

Definition two_sc (r : prop -> prop -> Prop) :=
  forall b1 b2 b1' b2', r b1 b2 -> subset b1' b1 -> subset b2' b2 -> r b1' b2'.

Lemma two_scP' :
  (forall P1 P2 r, two_sc r -> ((hrsat2 P1 P2 r) -> hrsat2 (P1↓) (P2↓) r)) <->
  (forall P1 P2 r, two_sc r -> ((exists Ct, ~ r (beh (Ct [P1↓])) (beh (Ct [P2↓]))) ->
                            (exists Cs, ~ r (beh (Cs [P1])) (beh (Cs [P2]))))).
Proof.
  split.
  + intros r2p P1 P2 r Hr [Ct nr].
    rewrite <- not_forall_ex_not.
    intros H. specialize (r2p P1 P2 r Hr H). now apply nr. 
  + intros r2pc P1 P2 r Hr H. unfold hrsat2.  
    intros Ct. rewrite dne. intros Hf.
    destruct (r2pc P1 P2 r Hr) as [Cs Hc].
    now exists Ct. now apply Hc.
Qed.     
    
Lemma two_scC :
  (forall P1 P2 r, two_sc r -> ((hrsat2 P1 P2 r) -> hrsat2 (P1↓) (P2↓) r)) <->
  (forall (P1 P2 : par src) Ct, exists Cs,
        (beh (Ct [P1↓])) ⊆  (beh (Cs [P1])) /\
        (beh (Ct [P2↓])) ⊆  (beh (Cs [P2]))).
Proof.
  rewrite two_scP'. split. 
  + intros r2sscP P1 P2 Ct.
    destruct (r2sscP P1 P2
                (fun π1 π2 => ~ subset (beh (Ct [P1 ↓])) π1 \/ ~ subset (beh (Ct [P2 ↓])) π2)) as [Cs Hcs].
    { intros b1 b2 b1' b2' [nsup1 | nsup2] s1 s2. 
      + left. unfold "⊆" in *. rewrite not_forall_ex_not in *.
        destruct nsup1 as [t Hn1]. exists t. 
        rewrite not_imp in *. split; firstorder.
      + right. unfold "⊆" in *; rewrite not_forall_ex_not in *. 
        destruct nsup2 as [t Hn2]. exists t. 
        rewrite not_imp in *. split; firstorder. }  
    exists Ct. rewrite de_morgan2. split; now rewrite <- dne. 
    rewrite de_morgan2 in Hcs. repeat (rewrite <- dne in Hcs). 
    now exists Cs.
  + intros scC P1 P2 r r2ssc [Ct nr]. destruct (scC P1 P2 Ct) as [Cs [K1 K2]].
    exists Cs. intros Hf. apply nr. unfold two_sc in r2ssc. eapply r2ssc; eassumption. 
Qed.     

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

Lemma RTP_R2SSCP : RC ->  (forall P1 P2 r, two_sc r -> ((hrsat2 P1 P2 r) -> hrsat2 (P1↓) (P2↓) r)). 
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


