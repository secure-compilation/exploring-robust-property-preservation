Require Import ClassicalExtras.
Require Import Setoid.
Require Import Events.
Require Import CommonST.
Require Import TraceModel.
Require Import Robustdef.
Require Import Properties. 
Require Import Topology.
Require Import XPrefix. 

(** This file proves the alternative, property-free criteria
    for the robust preservation of classes of properties *) 

(*********************************************************)
(* PROPERTIES                                            *)
(*********************************************************)

(** *Trace Properties *)
Definition RTC : Prop :=
  forall P C' t, exists C,
      sem tgt  (C' [ P ↓ ] ) t ->
      sem src  (C  [ P  ] ) t.

(*
   assuming there exists a source context and using
   classical logic we can move the existential in RC
   after the implication.
 *)
Axiom some_ctx_src : ctx src.

Lemma RTC' : RTC <-> (forall P C' t, sem tgt  (C' [ P ↓ ] ) t ->
                         exists C, sem src  (C  [ P  ] ) t).
Proof.
  unfold RTC. split.
  - intros rc P C' t H0. destruct (rc P C' t) as [C H1]. clear rc.
    exists C. apply (H1 H0).
  - intros rc' P C' t.
    assert (K : sem tgt  (C' [ P ↓ ] ) t \/ ~ sem tgt  (C' [ P ↓ ] ) t)
      by now apply classic.
    destruct K as [k | k].
    + destruct (rc' P C' t k) as [C H]. clear rc'.
      exists C. auto.
    + exists some_ctx_src. intros H. exfalso. apply (k H).
Qed.

(* RTC is equivalent to the preservation of robust satisfaction of every property *)
Theorem RTC_RTP : RTC <-> RTP.
Proof.
  rewrite RTC'. split.
  - intros rc P π. rewrite contra_RP.
    intros [C' [t' [H0 H1]]].
    destruct (rc P C' t' H0) as [C H]. clear rc. exists C,t'. auto.
  - intros rp P C' t H. specialize (rp P (fun b => b <> t)).
    rewrite contra_RP in rp. destruct rp as [C [t' [H0 H1]]].
    exists C',t. auto. apply NNPP in H1. subst t'. now exists C.
Qed.

Theorem RTC_RTP_maybe_simpler : RTC <-> (forall P π, RP P π).
Proof.
  unfold RP, rsat, sat. split.
  - unfold RTC.
    intros HRTC P π HsatCP Ct t HsemCtPC. destruct (HRTC P Ct t) as [Cs HTRC']. eauto.
  - rewrite RTC'. intros HRTP P. apply HRTP. eauto.
    (* here's a more detailed forwards proof *)
    (* pose proof (HRTP P (fun t => exists Cs, sem src (Cs[P]) t)) as HRTP'. simpl in HRTP'. *)
    (* assert(G : forall Cs t, sem src (Cs [P]) t -> exists Cs, sem src (Cs [P]) t) by eauto. *)
    (* specialize (HRTP' G). assumption. *)
Qed.


(** *Safety Properties *)

Definition RSC : Prop :=
  forall P C' t, sem tgt (C' [ P ↓ ] ) t ->
    forall m, (prefix m t -> exists C t', sem src (C [ P ] ) t' /\ prefix m t').

(*
   robustly safe compilation criterium is equivalent to the
   preservation of robust satisfaction of all Safety properties
 *)
Theorem RSC_RSP : RSC <-> RSP.
Proof.
 unfold RSC. split.
 - intros rsc P π S. rewrite contra_RP. intros [C' [t [H0 H1]]].
   destruct (S t H1) as [m [pmt S']].
   destruct (rsc P C' t H0 m pmt) as [C [t' [K0 pmt']]].
   exists C, t'. specialize (S' t' pmt'). now auto.
 - intros rsp P C' t H0 m pmt.
   assert (s : Safety (fun b => ~ prefix m b)).
   { unfold Safety. intros b H. apply NNPP in H. exists m. split.
     + assumption.
     + intros b' H' c. apply (c H'). }
   specialize (rsp P (fun b => ~ prefix m b) s).
   rewrite contra_RP in rsp. destruct rsp as [C [t' [K0 K1]]].
   exists C', t. now auto. apply NNPP in K1.
   now exists C,t'.
Qed.

(** ** Stronger variant of Robustly Safe Compilation *)
Lemma stronger_rsc (es : endstate) : (forall P C' t, sem tgt ( C' [ P ↓ ]) t  ->
  forall m, prefix m t -> exists C, sem src ( C [ P ] ) (embedding es m))
  -> RSC.
Proof.
  unfold RSC. intros H P c t Hsem' m Hprefix.
  specialize (H P c t Hsem' m Hprefix). destruct H as [C Hsem].
  exists C. exists (embedding es m). split. assumption. apply embed_pref.
Qed.

(* The reverse direction doesn't hold *)



(** *Liveness Properties *)

Definition RDC : Prop :=
  forall P C' t, inf t ->
     (exists C, sem tgt ( C' [ P ↓ ]) t ->
           sem src ( C [ P ]) t).

(* the same as for RC *)
Lemma RDC' : RDC <-> (forall P C' t, inf t -> sem tgt ( C' [ P ↓ ]) t ->
                                  exists C,  sem src ( C [ P ]) t).
Proof.
   unfold RDC. split.
  - intros rc P C' t Hi H0. destruct (rc P C' t) as [C H1]. clear rc.
    assumption. exists C. apply (H1 H0).
  - intros rc' P C' t Hi.
    assert (K :  sem tgt ( C' [ P ↓ ]) t \/ ~  sem tgt ( C' [ P ↓ ]) t)
      by now apply classic.
    destruct K as [k | k].
    + destruct (rc' P C' t Hi k) as [C H]. clear rc'.
      exists C. auto.
    + exists some_ctx_src. intros H. exfalso. apply (k H).
Qed.

Theorem RDC_RDP : RDC <-> (forall P π, Liveness π -> RP P π).
Proof.
  rewrite RDC'. split.
  - intros rlc P π Hl. rewrite contra_RP. intros [C' [t [H0 H1]]].
    assert(Hi : inf t) by (rewrite (not_in_liv_inf π) in Hl; now apply ( Hl t H1)).
    destruct (rlc P C' t Hi H0) as [C K0]. clear rlc.
    now exists C,t.
  - intros rlp P C' t Hi H0.
    specialize (rlp P (fun b => b <> t) (inf_excluded_is_liv t Hi)).
    rewrite contra_RP in rlp. destruct rlp as [C [t' [K0 K1]]].
    now exists C', t. apply NNPP in K1. subst t'.
    now exists C.
Qed.

(*********************************************************)
(* Criterium for Observable Properties Preservation
            
(* 

Without the constructor tsilent for traces 
(or equivalently when silent divergence is observable)
it is possible to show that the robsust preservation of 
all observable properties implies the robust preservation 
of all arbitrary properties. 
When silent divergence is not observable this is no more true 

Theorem RobsP_RPP : (forall P π, Observable π -> RP P π) <->
                    (forall P π, RP P π).
Proof.
  split; try now firstorder.
  intros hr P π. rewrite contra_RP.
  intros [C' [t [hsem ht]]].
  specialize (hr P (fun b => ~ t_eq t b)).
  assert (Observable (fun b => ~ t_eq t b)).
    (* This is False!! 
       e.g. when t = tstop 
       then the trace tsilent is in the property 
       but its only prefix, (ftbd nil) is also a prefix of tstop 
    *) 
     

Theorem RobsP_RTC : (forall P π, Observable π -> RP P π) <-> RTC.
Proof. now rewrite RobsP_RPP, RTC_RTP. Qed.

*) *)

(******************************************************************************)

(*********************************************************)
(* HYPERPROPERTIES                                       *)
(*********************************************************)


Require Import FunctionalExtensionality.
(* Require Import Logic.ClassicalFacts. *)


(** *HyperProperties *)
Definition RHC : Prop :=
  forall P C',
    (exists C, (forall t,  sem tgt ( C' [ P ↓ ]) t  <->  sem src ( C [ P ]) t)).

Lemma Hequiv_lemma : forall (π1 π2 : prop) (H : hprop),
     (forall t, π1 t <-> π2 t) ->
     (H π1 <-> H π2).
Proof.
  intros π1 π2 H H0. assert (π1 = π2).
  { apply functional_extensionality.
    intros t. specialize (H0 t). now apply prop_ext. }
  now subst.
Qed.


Theorem RHC_RHP : RHC <-> RHP.
Proof.
  split.
  - intros H0 P H. rewrite contra_RHP. intros [C' H1].
    specialize (H0 P C'). destruct H0 as [C H0].
    exists C. intros ff. eapply Hequiv_lemma in ff.
    apply (H1 ff). now auto.
  - unfold RHC. intros hrp P C'.
    specialize (hrp P (fun π => π <>  (sem tgt ( C' [ P ↓ ])))).
    rewrite contra_RHP in hrp. destruct hrp as [C H0].
    exists C'. rewrite <- dne. now auto.
    rewrite <- dne in H0. exists C. intros t.
    now  rewrite <- H0.
Qed.

(** *Subset-Closed Hyperproperties*)

Definition RSCHC : Prop :=
  forall P C',
  exists C, forall b,  sem tgt ( C' [ P ↓ ]) b ->  sem src ( C [ P ]) b.


Lemma RSCHC_RSCHP : RSCHC <-> RSCHP.
Proof.
  split.
   - intros ssc P H HH. rewrite contra_RHP. intros [C' H0].
     destruct (ssc P C') as [C h0]. exists C. now firstorder.
   - unfold RSCHC. intros h0 P C'.
     assert  (s : SSC (fun π => ~(forall b,  sem tgt ( C' [ P ↓ ]) b -> π b))).
     { unfold SSC. intros π h1 k Hk ff.
       assert (foo : forall b,  sem tgt ( C' [ P ↓ ]) b -> π b) by now auto.
       now apply (h1 foo). }
     specialize (h0 P (fun π => ~(forall b,  sem tgt ( C' [ P ↓ ]) b -> π b)) s).
     rewrite contra_RHP in h0.
     destruct h0 as [C h1]. exists C'.
     now rewrite <- dne. rewrite <- dne in h1.
     now exists C.          
Qed.


(** *2Subset-Closed Hyperproperties*)
Definition R2SCHC :=
  forall P Ct t1 t2,
      (sem tgt (Ct [P ↓]) t1 /\ sem tgt (Ct [P ↓]) t2)
      -> exists Cs, (sem src (Cs [P ]) t1 /\ sem src (Cs [P ]) t2).

Theorem R2SCHC_R2SCHP : R2SCHC <-> R2SCHP.
Proof.
  split.
    - intros ssc P H HH. rewrite contra_RHP. intros [C' H0].
    specialize (ssc P C'). unfold twoSC in HH. destruct HH as [t1 [t2 HH]].
    specialize (ssc t1 t2). destruct ssc as [C h0].
    split; firstorder.
    exists C. firstorder.
  - unfold R2SCHC. intros h0 P C' t1 t2 [H1 H2].
    specialize (h0 P).
    assert (s : twoSC (fun π => (~(sem tgt ( C' [ P ↓ ]) t1 -> π t1)) \/ (~(sem tgt ( C' [ P ↓ ]) t2 -> π t2)))).
    { unfold twoSC. intros. exists t1, t2. intros b. split.
      intros. apply de_morgan2 in H. destruct H as [H1' H2'].
      apply dne in H1'. apply dne in H2'. split; auto.
      intros H. apply de_morgan2. split; rewrite <- dne; destruct H; intros; try assumption.
    }
    specialize (h0 (fun π => (~(sem tgt ( C' [ P ↓ ]) t1 -> π t1)) \/ (~(sem tgt ( C' [ P ↓ ]) t2 -> π t2)))).
    specialize (h0 s).
    rewrite contra_RHP in h0.
    destruct h0 as [C h1]. exists C'.
    apply de_morgan2; split; now rewrite <- dne.
    apply de_morgan2 in h1; destruct h1 as [h1 h2];
      rewrite <- dne in h1; rewrite <- dne in h2.
    exists C; split; tauto.
Qed.


(** *HyperSafety *)
Definition RHSC : Prop :=
  forall P C' M, Observations M ->
            spref M (sem tgt ( C' [ P ↓ ]))  ->
            exists C, spref M (sem src ( C [ P])).

Theorem RHSC_RHSP : RHSC <-> RHSP.
Proof.
  split.
  - intros hsrc P H hs. rewrite contra_RHP. intros [C' h0].
    destruct (hs (fun b : trace => sem tgt ( C' [ P ↓ ]) b)) as [M [hm0 [hm1 hm2]]].
    assumption. destruct (hsrc P C' M) as [C hh]; auto.
    exists C. now apply hm2.
  - unfold RHSC. intros h P C' M h0 h1.
    assert (hs : HSafe (fun π => ~ spref M π)).
    { unfold HSafe. intros T hm. rewrite <- dne in hm.
      exists M. split; now auto. }
    specialize (h P (fun π => ~ spref M π) hs). rewrite contra_RHP in h.
    destruct h as [C hh]. now exists C'. exists C. now apply NNPP.
Qed.

(** *2HyperSafety *)
Definition R2HSC := forall P Ct, forall m1 m2,
        (spref (fun m => m = m1 \/ m = m2) (sem tgt ( Ct [ P ↓]))
         -> exists Cs, spref (fun m => m = m1 \/ m = m2) (sem src ( Cs [ P]))).

Theorem R2HSC_R2HSP : R2HSC <-> R2HSP.
Proof.
  split.
  - intros hsrc P H hs. rewrite contra_RHP. intros [C' h0].
    destruct (hs (fun b => sem tgt (C' [P ↓]) b)) as [m1 [m2 [H1 H2]]].
    assumption.
    destruct (hsrc P C' m1 m2) as [C hh]; auto.
    exists C. now apply H2.
  - unfold R2HSC.
    intros. specialize (H P).
    assert (hs : H2Safe (fun π => ~ spref (fun m => m = m1 \/ m = m2) π)).
    { clear. unfold H2Safe. intros b hm. rewrite <- dne in hm.
      exists m1, m2. split. assumption. now auto. }
    specialize (H (fun π => ~ spref (fun m => m = m1 \/ m = m2) π) hs).
    rewrite contra_RHP in H. destruct H as [C hh].
    now exists Ct. exists C. now apply NNPP.
Qed.

Lemma R2HSC_RSC : R2HSC -> RSC. 
Proof.
  intros H P Ct t Ht m Hpref.
  destruct (H P Ct m m) as [Cs Hspref].
  intros m' [K | K]; subst; now exists t.
  exists Cs. destruct (Hspref m) as [t' H']; simpl; auto.
Qed.

Lemma R2SCHC_R2HSC : R2SCHC -> R2HSC.
Proof. 
  intros rsc P Ct m1 m2 H. unfold spref in *.
  destruct (H m1) as [t1 [Ht1 Hpref1]]; auto.   
  destruct (H m2) as [t2 [Ht2 Hpref2]]; auto.
  specialize (rsc P Ct t1 t2). destruct rsc as [Cs [K1 K2]]; auto.
  exists Cs. intros x [H1 | H2]; subst; [now exists t1 | now exists t2].
Qed.


(** *HyperLiveness *)

(*********************************************************)
(* Criterium for HyperLiveness Preservation
   is the same as the one for
   all Hyperproperties Preservation                      *)
(*********************************************************)

Lemma bad_HyperLiv : forall C' P,
    HLiv (fun π : prop => π <> (sem tgt ( C' [ P ↓ ] ))).
Proof.
  unfold HLiv. intros C' P M obsM.
  assert (sem tgt (C' [P ↓]) = Embedding M \/  sem tgt (C' [P ↓]) <> Embedding M)
    by now apply classic.
  destruct H.
  + rewrite H; clear H. exists (fun t =>
                             (exists m es, M m /\ t = embedding es m) \/
                                       t = tstream (constant_stream an_event)).
    split.
    ++ unfold spref. intros m hm. exists (embedding an_endstate m).
       split.
       +++ left. now exists m, an_endstate.
       +++ now apply embed_pref.
     ++ intros hf. apply (infinite_trace_not_in_embed M).
        rewrite <- hf. now right.
  + exists (Embedding M). split; try now auto.
    unfold spref, Embedding. intros m hm.
    exists (embedding an_endstate m). split.
    ++ now exists m, an_endstate.
    ++ now apply embed_pref.
Qed.

Theorem RHC_RHLP : RHC <-> RHLP.
Proof.
 rewrite RHC_RHP. split; try now firstorder.
 intros rhlp P H. rewrite contra_RHP. intros [C' K].
 specialize (rhlp P (fun π : prop => π <> sem tgt (C' [ P ↓]) ) (bad_HyperLiv C' P)).
 rewrite contra_RHP in rhlp.
 destruct rhlp as [C KK]. exists C'. now rewrite <- dne. apply NNPP in KK.
 exists C. now rewrite KK.
Qed.

Theorem RHLP_RHP :
    RHLP <-> RHP.
Proof. now rewrite <- (RHC_RHP), (RHC_RHLP). Qed.


(*********************************************************)
(* RELATIONS                                             *)
(*********************************************************)

(** *2Relational Trace Properties *)

Definition R2rTC := forall Ct P1 P2 t1 t2,
  sem tgt (Ct [P1 ↓]) t1 ->  sem tgt (Ct [P2 ↓]) t2 ->
  exists Cs, sem src (Cs [P1]) t1 /\ sem src (Cs [P2]) t2.

Lemma R2rTC_R2rTP : R2rTC <-> R2rTP.
Proof.
  rewrite R2rTP'. unfold R2rTP, R2rTC. split.
  - intros H P1 P2 r Ct t1 t2 H1 H2 Hr.
    specialize (H Ct P1 P2 t1 t2 H1 H2).
    destruct H as [Cs [G1 G2]]. now exists Cs, t1, t2.
  - intros H Ct P1 P2 t1 t2 H1 H2.
    specialize (H P1 P2 (fun t1' t2' => t1' <> t1 \/ t2' <> t2)).
    assert(Htriv: ~ (t1 <> t1 \/ t2 <> t2)) by tauto.
    simpl in H. specialize (H Ct t1 t2 H1 H2 Htriv).
    destruct H as [Cs [t1' [t2' [H1' [H2' Heq]]]]].
    exists Cs. rewrite de_morgan2 in Heq. destruct Heq as [Heq1 Heq2].
    apply NNPP in Heq1. apply NNPP in Heq2. subst. tauto.
Qed.

(*************************************************************************)
(* If the source language is deterministic than
    R2rTC =>  RTEP (trace equivalence preservation)                      *)
(*************************************************************************)


Section source_determinism.

  Hypothesis src_det : forall P t1 t2, sem src P t1 -> sem src P t2 -> t1 = t2.

  Theorem R2rTC_RTEP : R2rTC -> RTEP.
  Proof.
    unfold R2rTC. rewrite RTEP'. intros H P1 P2 [Ct [t' H']].
    rewrite not_iff in H'. destruct H' as [[H1' nH2'] | [nH1' H2']].
    - destruct (non_empty_sem tgt (Ct [P2 ↓])) as [t2 H2'].
      destruct (H _ _ _ _ _ H1' H2') as [Cs [H1 H2]].
      exists Cs, t2. intros Hf. rewrite <- Hf in H2.
      specialize (src_det (Cs [P1] ) t' t2 H1 H2). now subst.
    - destruct (non_empty_sem tgt (Ct [P1 ↓])) as [t1 H1'].
      destruct (H _ _ _ _ _ H1' H2') as [Cs [H1 H2]].
      exists Cs, t'. intros Hf. rewrite <- Hf in H2.
      specialize (src_det (Cs [P1] ) t1 t' H1 H2). now subst.
   Qed.

End source_determinism.


(** *Arbitrary Relational Trace Properties *)

Definition RrTC :=
  forall (f : par src -> trace) Ct,
    (forall P, sem tgt (Ct [P↓]) (f P)) ->
    exists Cs, (forall P, sem src (Cs [P]) (f P)).

Lemma RrTC_RrTP : RrTC <-> RrTP.
Proof.
  split.
  - intros HRrTC R. rewrite contra.
    intros Htgt. rewrite not_forall_ex_not in Htgt.
    destruct Htgt as [Ct Htgt]. rewrite not_forall_ex_not in Htgt.
    destruct Htgt as [f Htgt]. rewrite not_forall_ex_not in Htgt.
    destruct Htgt as [Htgt H]. destruct (HRrTC f Ct Htgt) as [Cs HCs].   
    intro Hsrc. apply H. now apply (Hsrc Cs).     
  - intros HRrTP f Ct Htgt. specialize (HRrTP (fun g => g <> f)).
    rewrite contra in HRrTP. repeat rewrite not_forall_ex_not in HRrTP.
    destruct HRrTP as [Cs H1].
    { exists Ct. rewrite not_forall_ex_not. exists f.
      rewrite not_forall_ex_not.  exists Htgt. now rewrite <- dne. }
    exists Cs. rewrite not_forall_ex_not in H1. destruct H1 as [f' H1].
    rewrite not_forall_ex_not in H1. destruct H1 as [H1 HH1].
    rewrite <- dne in HH1. now subst. 
Qed.      


(** *2Relational Safety Properties *)

Definition R2rSC := forall Ct P1 P2 m1 m2,
    psem (Ct [P1↓]) m1 -> psem (Ct [P2↓]) m2 ->
    exists Cs, psem (Cs [P1]) m1 /\ psem (Cs [P2]) m2.

Theorem R2rSC_R2rSP : R2rSC <-> R2rSP.
Proof.
  rewrite R2rSP'. unfold R2rSP, R2rSC. split.
  - intros H P1 P2 r Hsafety Ct t1 t2 H1 H2 Hr.
    specialize (H Ct P1 P2).
    unfold safety2 in Hsafety. specialize (Hsafety t1 t2 Hr).
    destruct Hsafety as [m1 [m2 [Hm1 [Hm2 Hs]]]].
    specialize (H m1 m2). unfold psem in H.
    assert (Hex1 : (exists t : trace, prefix m1 t /\ sem _ (plug _ (P1 ↓) Ct) t)).
    { exists t1; auto. }
    assert (Hex2 : (exists t : trace, prefix m2 t /\ sem _ (plug _ (P2 ↓) Ct) t)).
    { exists t2; auto. }
    specialize (H Hex1 Hex2). destruct H as [Cs [HCs1 HCs2]].
    unfold psem in HCs1. unfold psem in HCs2. destruct HCs1 as [t1' [Hpref1' Hsem1']].
    destruct HCs2 as [t2' [Hpref2' Hsem2']].
    exists Cs, t1', t2'. auto.
  - intros H Ct P1 P2 m1 m2 H1 H2.
    specialize (H P1 P2 (fun t1' t2' => ~ (prefix m1 t1') \/ ~(prefix m2 t2'))).
    assert (Hsafety : safety2 (fun t1' t2' => ~ (prefix m1 t1') \/ ~(prefix m2 t2'))).
    { clear. unfold safety2.
      intros t1 t2 Ht. apply not_or_and in Ht. destruct Ht as [Ht1 Ht2].
      apply NNPP in Ht1. apply NNPP in Ht2.
      exists m1. exists m2. firstorder. }
    unfold psem in H1, H2. destruct H1 as [t1 [H1 H1']]. destruct H2 as [t2 [H2 H2']].
    specialize (H Hsafety Ct t1 t2 H1' H2').
    assert (Htriv : ~ (fun t1' t2' : trace => ~ prefix m1 t1' \/ ~ prefix m2 t2') t1 t2).
    { apply and_not_or. split; firstorder. }
    specialize (H Htriv).
    destruct H as [Cs [t1' [t2' [Ht1' [Ht2' H]]]]].
    exists Cs.
    assert (Htriv' : ~ (fun t1' t2' : trace => ~ prefix m1 t1' \/ ~ prefix m2 t2') t1' t2').
    { apply and_not_or. split; firstorder. }
    simpl in Htriv'. apply not_or_and in Htriv'. destruct Htriv' as [Htriv1' Htriv2'].
    apply NNPP in Htriv1'. apply NNPP in Htriv2'.
    split; unfold psem.
    exists t1'; auto. exists t2'; auto.
Qed.

(* the following is another characterization of R2rSC *)
Definition R2rSC' : Prop :=
  forall P1 P2 (r : finpref -> finpref -> Prop),
    ((forall Cs m1 m2, psem (Cs [P1]) m1 -> psem (Cs [P2]) m2 -> r m1 m2) ->
     (forall Ct m1 m2, psem (Ct [P1 ↓]) m1 -> psem (Ct [P2 ↓]) m2 -> r m1 m2)).

Theorem R2rSC_R2rSC' : R2rSC <-> R2rSC'.
Proof.
  unfold R2rSC, R2rSC'.
  split.
  - intros H P1 P2 r H' Ct m1 m2 Hsem1 Hsem2.
    specialize (H Ct P1 P2 m1 m2 Hsem1 Hsem2).
    destruct H as [Cs [Hsem1' Hsem2']].
    specialize (H' Cs m1 m2 Hsem1' Hsem2'). now assumption.
  - intros H Ct P1 P2 m1 m2 Hsem1 Hsem2.
    specialize (H P1 P2).
    specialize (H (fun m1 m2 => exists Cs, psem (Cs [P1]) m1 /\ psem (Cs [P2]) m2)); simpl in H.
    assert (H' : forall Cs m1 m2, psem (Cs [P1]) m1 -> psem (Cs [P2]) m2 ->
                             (exists Cs, psem (Cs [P1]) m1 /\ psem (Cs [P2]) m2)).
    { clear. intros Cs m1 m2 Hsem1 Hsem2. exists Cs; now auto. }
    specialize (H H' Ct m1 m2 Hsem1 Hsem2). now assumption.
Qed.

Theorem R2rSP_R2rSC' : R2rSP <-> R2rSC'.
Proof.
  now rewrite <- R2rSC_R2rSP, R2rSC_R2rSC'.
Qed.


(** *Arbitrary Relational Safety Properties *)

Definition RrSC : Prop :=
  forall Ct (f : par src -> (finpref -> Prop)),
    (forall P, spref (f P) (sem tgt (Ct [P↓]))) ->
    exists Cs,  (forall P, spref (f P) (sem src (Cs [P]))).

Theorem RrSC_RrSP : RrSC <-> RrSP.
Proof.
  unfold RrSP, RrSC. split.
  - intros h R h0 Ct f h1. specialize (h Ct f h1).
    destruct h as [Cs h]. now apply (h0 Cs f h).
  - intros h Ct f h0. apply NNPP. intros ff.
    rewrite not_ex_forall_not in ff.
    specialize (h (fun g => exists Cs, forall P, spref (g P) (sem src (Cs [P])))).
    simpl in *.
    assert(hh :  (forall (Cs : ctx src) (f : par src -> fprop),
       (forall P : par src, spref (f P) (sem src (Cs [P]))) ->
       exists Cs0 : ctx src,
         forall P : par src, spref (f P) (sem src (Cs0 [P])))).
    { intros Cs f0 hhh. now exists Cs. }
    destruct (h hh Ct f h0) as [Cs hhh]. clear hh h.
    specialize (ff Cs). now auto.
Qed.


(** *2Relational XSafety Properties *)

Definition R2rXC := forall Ct P1 P2 x1 x2,
   xsem (Ct [P1↓]) x1 -> xsem (Ct [P2↓]) x2 ->
  exists Cs, xsem (Cs[P1]) x1 /\ xsem (Cs[P2]) x2.


Theorem R2rXC_R2rXP : R2rXC <-> R2rXP.
Proof.
  rewrite R2rXP'. unfold R2rXP, R2rXC. split.
  - intros H P1 P2 r Hsafety Ct t1 t2 H1 H2 Hr.
    specialize (H Ct P1 P2).
    unfold safety2 in Hsafety. specialize (Hsafety t1 t2 Hr).
    destruct Hsafety as [m1 [m2 [Hm1 [Hm2 Hs]]]].
    specialize (H m1 m2). unfold psem in H.
    assert (Hex1 : (exists t : trace, xprefix m1 t /\ sem _ (plug _ (P1 ↓) Ct) t)).
    { exists t1; auto. }
    assert (Hex2 : (exists t : trace, xprefix m2 t /\ sem _ (plug _ (P2 ↓) Ct) t)).
    { exists t2; auto. }
    specialize (H Hex1 Hex2). destruct H as [Cs [HCs1 HCs2]].
    unfold psem in HCs1. unfold psem in HCs2. destruct HCs1 as [t1' [Hpref1' Hsem1']].
    destruct HCs2 as [t2' [Hpref2' Hsem2']].
    exists Cs, t1', t2'. auto.
  - intros H Ct P1 P2 m1 m2 H1 H2.
    specialize (H P1 P2 (fun t1' t2' => ~ (xprefix m1 t1') \/ ~(xprefix m2 t2'))).
    assert (Hsafety : xafety2 (fun t1' t2' => ~ (xprefix m1 t1') \/ ~(xprefix m2 t2'))).
    { clear. unfold xafety2.
      intros t1 t2 Ht. apply not_or_and in Ht. destruct Ht as [Ht1 Ht2].
      apply NNPP in Ht1. apply NNPP in Ht2.
      exists m1. exists m2. firstorder. }
    unfold psem in H1, H2. destruct H1 as [t1 [H1 H1']]. destruct H2 as [t2 [H2 H2']].
    specialize (H Hsafety Ct t1 t2 H1' H2').
    assert (Htriv : ~ (fun t1' t2' : trace => ~ xprefix m1 t1' \/ ~ xprefix m2 t2') t1 t2).
    { apply and_not_or. split; firstorder. }
    specialize (H Htriv).
    destruct H as [Cs [t1' [t2' [Ht1' [Ht2' H]]]]].
    exists Cs.
    assert (Htriv' : ~ (fun t1' t2' : trace => ~ xprefix m1 t1' \/ ~ xprefix m2 t2') t1' t2').
    { apply and_not_or. split; firstorder. }
    simpl in Htriv'. apply not_or_and in Htriv'. destruct Htriv' as [Htriv1' Htriv2'].
    apply NNPP in Htriv1'. apply NNPP in Htriv2'.
    split; unfold psem.
    exists t1'; auto. exists t2'; auto.
Qed.

Definition  R2rXC' : Prop :=
  forall (r : xpref -> xpref -> Prop) P1 P2 ,
    ((forall Cs x1 x2, xsem (Cs [P1]) x1 ->
                  xsem (Cs [P2]) x2 ->
                   r x1 x2) ->
     (forall Ct x1 x2, xsem (Ct [P1 ↓]) x1 ->
                  xsem (Ct [P2 ↓]) x2 ->
                  r x1 x2)).

Lemma R2rXC_R2rXC' : R2rXC <-> R2rXC'.
Proof.
  unfold R2rXC, R2rXC'. split.
   - intros H r P1 P2 H' Ct m1 m2 Hsem1 Hsem2.
    specialize (H Ct P1 P2 m1 m2 Hsem1 Hsem2).
    destruct H as [Cs [Hsem1' Hsem2']].
    specialize (H' Cs m1 m2 Hsem1' Hsem2'). now assumption.
  - intros H Ct P1 P2 m1 m2 Hsem1 Hsem2.
    specialize (H (fun m1 m2 => exists Cs, xsem (Cs [P1]) m1 /\ xsem (Cs [P2]) m2)); simpl in H.
    specialize (H P1 P2).    
    assert (H' : forall Cs m1 m2, xsem (Cs [P1]) m1 -> xsem (Cs [P2]) m2 ->
                             (exists Cs, xsem (Cs [P1]) m1 /\ xsem (Cs [P2]) m2)).
    { clear. intros Cs m1 m2 Hsem1 Hsem2. exists Cs; now auto. }
    specialize (H H' Ct m1 m2 Hsem1 Hsem2). now assumption. 
Qed.


(* Still R2rXP implies R2rSP, and one can prove it by looking at the
   property-free characterization. *)

Lemma R2rXC_R2rSC : R2rXC -> R2rSC.
Proof.
  unfold R2rXC, R2rSC. intros H Ct P1 P2 m1 m2 [t1 [H1 H1']] [t2 [H2 H2']].
  specialize (H Ct P1 P2 (xembed m1) (xembed m2)).
  apply prefix_xprefix_xembed in H1. apply prefix_xprefix_xembed in H2.
  assert (X1 : xsem (Ct [P1 ↓]) (xembed m1)) by (exists t1; tauto).
  assert (X2 : xsem (Ct [P2 ↓]) (xembed m2)) by (exists t2; tauto).
  specialize (H X1 X2). destruct H as [Cs [[t1' [XX1 Hsem1]] [t2' [XX2 Hsem2]]]].
  exists Cs. apply xprefix_xembed_prefix in XX1.
             apply xprefix_xembed_prefix in XX2. split.
  - exists t1'. tauto.
  - exists t2'. tauto.
Qed.


(** *2Relational HyperProperties *)

Definition R2rHC : Prop :=
  forall P1 P2 Ct, exists Cs, (sem src (Cs [P1]) = sem tgt (Ct [P1 ↓]))
                    /\ (sem src (Cs [P2]) = sem tgt (Ct [P2 ↓])).


Theorem R2rHC_R2rHP : R2rHC <-> R2rHP.
Proof.
  unfold R2rHP, R2rHC; split.
  - intros h P1 P2 r hcs Ct. destruct (h P1 P2 Ct) as [Cs [h0 h1]]; clear h.
    specialize (hcs Cs).
    rewrite h0, h1 in hcs. now assumption.
  - intros H2hrp P1 P2 Ct. apply NNPP. intros ff.
    rewrite not_ex_forall_not in ff.
    specialize (H2hrp P1 P2).
    specialize (H2hrp (fun f1 f2 => exists Cs, forall t, f1 t = sem src (Cs [ P1 ]) t
                                                   /\ f2 t = sem src (Cs [ P2 ]) t)).
    simpl in *.
    assert (hh : hrsat2 P1 P2
            (fun f1 f2 : prop =>
             exists Cs : ctx src,
               forall t : trace, f1 t = sem src (Cs [P1]) t /\ f2 t = sem src (Cs [P2]) t)).
    { clear. unfold hrsat2. intros. exists C. intros. split; now auto. }
    specialize (H2hrp hh Ct); clear hh.
    unfold hrsat2 in H2hrp. destruct H2hrp as [Cs h].
    specialize (ff Cs).
    assert (sem src (Cs [P1]) = sem tgt (Ct [P1 ↓])).
    { apply functional_extensionality. intros t. specialize (h t).
      destruct h as [h1 h2]. auto. }
    assert (sem src (Cs [P2]) = sem tgt (Ct [P2 ↓])).
    { apply functional_extensionality. intros t. specialize (h t).
      destruct h as [h1 h2]. auto. }
    apply ff. split; auto.
Qed. 


(** *Arbitrary Relational HyperProperties *)
Definition RrHC : Prop :=
  forall Ct, exists Cs,  (forall P, sem src (Cs [P]) = sem tgt (Ct [P ↓])).

Theorem RrHC_RrHP : RrHC <-> RrHP.
Proof.
  unfold RrHP, RrHC. split.
  - intros h R hcs Ct. destruct (h Ct) as [Cs h0]; clear h.
    specialize (hcs Cs).
    assert (hh :  (fun P : par src => sem src (Cs [P])) =
                  (fun P : par src => sem tgt (Ct [P ↓])) ).
    { apply functional_extensionality.
      intros P. specialize (h0 P). now auto. }
    now rewrite <- hh.
  - intros hrrhp Ct. apply NNPP. intros ff.
    rewrite not_ex_forall_not in ff.
    specialize (hrrhp (fun f => exists Cs, forall P, f P = sem src (Cs [ P ]) )).
    simpl in *.
    assert (hh : (forall Cs, exists Cs0, forall P, sem src (Cs [P]) = sem src (Cs0 [ P ]))).
    { intros Cs. now exists Cs. }
    specialize (hrrhp hh); clear hh.
    destruct (hrrhp Ct) as [Cs h].
    specialize (ff Cs). now apply ff.
Qed.


 
(** *2Relational SubsetClosed HyperProperties *)
Definition R2rSCHC:=  (forall (P1 P2 : par src) Ct, exists Cs,
                            (beh (Ct [P1↓])) ⊆  (beh (Cs [P1])) /\
                            (beh (Ct [P2↓])) ⊆  (beh (Cs [P2]))).


Theorem R2rSCHC_R2rSCHP : R2rSCHC <-> R2rSCHP. 
  rewrite R2rSCHP'. split. 
  + intros scC P1 P2 r r2ssc [Ct nr]. destruct (scC P1 P2 Ct) as [Cs [K1 K2]].
    exists Cs. intros Hf. apply nr. unfold ssc2 in r2ssc. eapply r2ssc; eassumption.
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
Qed.     

