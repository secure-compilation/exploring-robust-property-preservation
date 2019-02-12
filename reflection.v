Require Import Events.  
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Criteria. 
Require Import ClassicalExtras.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.

(** This file proves the collapses that happens in presence of
    reflection in the source language *)

(* 

       RrHP  ---  
                 \ 
        |  ----- RrSCP --- 
          /      /         \ 
       RHP      /          RrTP ---
(<-> RFrSCP)   /           /       \  
        |     /---------- /          RrSP
                         /          /
     RSCP (<-> RFrTP)   /          /
                       /          / 
        |             /          /
                     /          /
       RTP --------- --        /
                       \      /
      /   \             RHSP (<-> RFrSP)
                       /
    RDP   RSP   -------

*)


Variable code_intro : forall {P1 P2 : par src} (h : P1 <> P2) (Cs1 Cs2 : ctx src), ctx src. 

Axiom beh_intro1 : forall P1 P2 (h : P1 <> P2)Cs1 Cs2,
    forall t,
     sem src ((code_intro h Cs1 Cs2) [P1]) t <-> sem src (Cs1 [P1]) t. 

Axiom beh_intro2 : forall P1 P2 (h : P1 <> P2) Cs1 Cs2,
    forall t,
    sem src ((code_intro h Cs1 Cs2) [P2]) t = sem src (Cs2 [P2]) t.                   

(* R2HSP -> r2RSP and a similar argument for k >= 2 *)
Lemma R2HSP_R2rSP : R2HSP -> R2rSP.
Proof.
  rewrite <- R2HSC_R2HSP, <- R2rSC_R2rSP.
  intros H2rsc Ct P1 P2 m1 m2 H1 H2.
  destruct H1 as [t1 [Hpref1 H1]]. 
  destruct H2 as [t2 [Hpref2 H2]].
  destruct (classic (P1 = P2)) as [Heq | Hneq]. 
  + rewrite <- Heq in *.  
    destruct (H2rsc P1 Ct m1 m2) as [Cs Hspref].
    ++ intros x [Hx | Hx]; [exists t1 | exists t2]; subst; auto.
    ++ exists Cs. split.
       +++ destruct (Hspref m1) as [tt1 Hpref11]; simpl; auto.
           now exists tt1.
       +++ destruct (Hspref m2) as [tt2 Hpref22]; simpl; auto.
           now exists tt2.
  + apply R2HSC_RSC in H2rsc.
    destruct (H2rsc P1 Ct t1 H1 m1 Hpref1) as [Cs1 [t1' [H' H'']]].
    destruct (H2rsc P2 Ct t2 H2 m2 Hpref2) as [Cs2 [t2' [H2' H2'']]]. 
    exists (code_intro Hneq Cs1 Cs2). 
    split; [exists t1' | exists t2'];
      split; auto; [  now rewrite (beh_intro1 P1 P2 Hneq Cs1 Cs2)
                    | now rewrite (beh_intro2 P1 P2 Hneq Cs1 Cs2)].
Qed.

(* RHP -> r2RHP *)

(* as usual we need prop_extensionality *)

Hypothesis prop_ext : prop_extensionality. 

Lemma RHP_R2rHP : RHP -> R2rHP.
Proof.
  rewrite <- RHC_RHP, <- R2rHC_R2rHP.
  intros hrc P1 P2 Ct.
  destruct (hrc P1 Ct) as [Cs1 H1].
  destruct (hrc P2 Ct) as [Cs2 H2].
  destruct (classic (P1 = P2)) as [Heq | Hneq].  
  + rewrite Heq in *.
    exists Cs1. split; apply functional_extensionality;
             intros t; apply prop_ext; now auto.
  + exists (code_intro Hneq Cs1 Cs2).
    split; apply functional_extensionality; intros t;
      apply prop_ext; 
    [ now rewrite beh_intro1 | now rewrite beh_intro2].
Qed.

(* RSCP -> R2rSCP *)

Lemma RSCP_R2rSCP : RSCHP -> R2rSCHP. 
Proof.
  rewrite <- R2rSCHC_R2rSCHP, <- RSCHC_RSCHP.    
  intros sscr P1 P2 Ct.
  destruct (classic (P1 = P2)) as [Heq | Hneq].
  + rewrite <- Heq in *. destruct (sscr P1 Ct) as [Cs H].
    now exists Cs.
  + destruct (sscr P1 Ct) as [Cs1 H1].
    destruct (sscr P2 Ct) as [Cs2 H2].
    exists (code_intro Hneq Cs1 Cs2).
    split; intros t H; [rewrite beh_intro1; now apply H1
                       | rewrite beh_intro2; now apply H2].        
Qed.


Lemma R2rSCP_R2rTP : R2rSCHP -> R2rTP.  
Proof.
  rewrite <- R2rSCHC_R2rSCHP, <- R2rTC_R2rTP.
  intros rp Ct P1 P2 t1 t2 H1 H2.
  destruct (rp P1 P2 Ct) as [Cs [HH1 HH2]].
  exists Cs; split; [now apply HH1 | now apply HH2].
Qed.

Theorem RSCHP_R2rTP : RSCHP -> R2rTP.
Proof.
  intros H. now apply R2rSCP_R2rTP; apply RSCP_R2rSCP. 
Qed.   
