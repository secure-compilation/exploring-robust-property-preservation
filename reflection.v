Require Import Events. 
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Criteria. 
Require Import ClassicalExtras.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts. 

Variable code_intro : forall {P1 P2 : par src} (h : P1 <> P2) (Cs1 Cs2 : ctx src), ctx src. 

(* CA: actually we only need beh to be equal, 
       but this way it is easier to rewrite 
*)
Axiom beh_intro1 : forall P1 P2 (h : P1 <> P2)Cs1 Cs2,
     (code_intro h Cs1 Cs2) [P1] = Cs1 [P1]. 

Axiom beh_intro2 : forall P1 P2 (h : P1 <> P2) Cs1 Cs2,
    (code_intro h Cs1 Cs2) [P2] = Cs2 [P2]. 

(* TODO: move to Criteria.v *)
Lemma R2HSP_RSP : H2SRC -> RSC. 
Proof.
  intros H P Ct t Ht m Hpref.
  destruct (H P Ct m m) as [Cs Hspref].
  intros m' [K | K]; subst; now exists t.
  exists Cs. destruct (Hspref m) as [t' H']; auto.
Qed.                      

(* R2HSP -> r2RSP and a similar argument for k >= 2 *)

Lemma R2HSP_r2RSP : (forall P H, H2Safe H -> RHP P H) -> r2RSP.
Proof.
  rewrite R2HSP_H2SRC, r2RSP_r2RSC.
  intros H2rsc Ct P1 P2 m1 m2 H1 H2.
  destruct H1 as [t1 [Hpref1 H1]]. 
  destruct H2 as [t2 [Hpref2 H2]].
  destruct (classic (P1 = P2)) as [Heq | Hneq]. 
  + rewrite <- Heq in *.  
    destruct (H2rsc P1 Ct m1 m2) as [Cs Hspref].
    ++ intros x [Hx | Hx]; [exists t1 | exists t2]; subst; auto.
    ++ exists Cs. split.
       +++ destruct (Hspref m1) as [tt1 Hpref11]; auto.
           now exists tt1.
       +++ destruct (Hspref m2) as [tt2 Hpref22]; auto.
           now exists tt2.
  + apply R2HSP_RSP in H2rsc.
    destruct (H2rsc P1 Ct t1 H1 m1 Hpref1) as [Cs1 [t1' [H' H'']]].
    destruct (H2rsc P2 Ct t2 H2 m2 Hpref2) as [Cs2 [t2' [H2' H2'']]]. 
    exists (code_intro Hneq Cs1 Cs2). 
    split; [rewrite (beh_intro1 P1 P2 Hneq Cs1 Cs2)
           | rewrite (beh_intro2 P1 P2 Hneq Cs1 Cs2)];
    [now exists t1' | now exists t2'].
Qed.

(* RHP -> r2RHP *)

(* as usual we need prop_extensionality *)

Hypothesis prop_ext : prop_extensionality. 

Lemma RHP_r2RHP : (forall P H, RHP P H) -> r2HRP.
Proof.
  rewrite <- HRC_RHP, r2HRP_r2HRC.
  intros hrc P1 P2 Ct.
  destruct (hrc P1 Ct) as [Cs1 H1].
  destruct (hrc P2 Ct) as [Cs2 H2].
  destruct (classic (P1 = P2)) as [Heq | Hneq].  
  + rewrite Heq in *.
    exists Cs1. split; apply functional_extensionality;
             intros t; apply prop_ext; now auto.
  + exists (code_intro Hneq Cs1 Cs2). rewrite beh_intro1, beh_intro2.
     split; apply functional_extensionality;
       intros t; apply prop_ext; now auto.
Qed.



(* TODO : move to Criteria.v *)

Infix "⊆" := subset (at level 50).

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

(* RSCP -> R2rSCP *)

Lemma RSCP_R2rSCP : ssc_cr -> (forall P1 P2 r, two_sc r -> ((hrsat2 P1 P2 r) -> hrsat2 (P1↓) (P2↓) r)).
Proof.
  rewrite two_scC. 
  intros sscr P1 P2 Ct.
  destruct (classic (P1 = P2)) as [Heq | Hneq].
  + rewrite <- Heq in *. destruct (sscr P1 Ct) as [Cs H].
    now exists Cs.
  + destruct (sscr P1 Ct) as [Cs1 H1].
    destruct (sscr P2 Ct) as [Cs2 H2].
    exists (code_intro Hneq Cs1 Cs2). rewrite beh_intro1, beh_intro2. 
    split; now auto.
Qed.
                                   