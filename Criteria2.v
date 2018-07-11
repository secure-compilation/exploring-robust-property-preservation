Require Import ClassicalExtras.
Require Import Setoid.
Require Import Events.
Require Import CommonST2.
Require Import TraceModel2.
Require Import Robustdef2.
Require Import Properties2.
Require Import Topology2.

(** *property free criteria *)


(*********************************************************)
(* Criterium for all Properties Preservation             *)
(*********************************************************)

Definition RC : Prop :=
  forall P C' t, exists C,
      sem tgt  (C' [ P ↓ ] ) t ->
      sem src  (C  [ P  ] ) t.

(*
   assuming there exists a source context and using
   classical logic we can move the existential in RC
   after the implication.
 *)
Axiom some_ctx : ctx src. 

Lemma RC' : RC <-> (forall P C' t, sem tgt  (C' [ P ↓ ] ) t ->
                        exists C, sem src  (C  [ P  ] ) t).
Proof.
  unfold RC. split.
  - intros rc P C' t H0. destruct (rc P C' t) as [C H1]. clear rc.
    exists C. apply (H1 H0).
  - intros rc' P C' t.
    assert (K : sem tgt  (C' [ P ↓ ] ) t \/ ~ sem tgt  (C' [ P ↓ ] ) t)
      by now apply classic.
    destruct K as [k | k].
    + destruct (rc' P C' t k) as [C H]. clear rc'.
      exists C. auto.
    + exists some_ctx. intros H. exfalso. apply (k H).
Qed.

(* RC is equivalent to the preservation of robust satisfaction of every property *)
Theorem RC_RPP : RC <-> (forall P π, RP P π).
Proof.
  rewrite RC'. split.
  - intros rc P π. rewrite contra_RP.
    intros [C' [t' [H0 H1]]].
    destruct (rc P C' t' H0) as [C H]. clear rc. exists C,t'. auto.
  - intros rp P C' t H. specialize (rp P (fun b => b <> t)).
    rewrite contra_RP in rp. destruct rp as [C [t' [H0 H1]]].
    exists C',t. auto. apply NNPP in H1. subst t'. now exists C.
Qed.


(*********************************************************)
(* Criterium for Safety Properties Preservation          *)
(*********************************************************)

Definition RSC : Prop :=
  forall P C' t, sem tgt (C' [ P ↓ ] ) t ->
    forall m, (prefix m t -> exists C t', sem src (C [ P ] ) t' /\ prefix m t').

(*
   robustly safe compilation criterium is equivalent to the
   preservation of robust satisfaction of all Safety properties
 *)
Theorem RSC_RSP : RSC <-> (forall P π, Safety π -> RP P π).
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
Lemma stronger_rsc : (forall P C' t, sem tgt ( C' [ P ↓ ]) t  ->
  forall m, prefix m t -> exists C, sem src ( C [ P ] ) (embedding m))
  -> RSC.
Proof.
  unfold RSC. intros H P c t Hsem' m Hprefix.
  specialize (H P c t Hsem' m Hprefix). destruct H as [C Hsem].
  exists C. exists (embedding m). split. assumption. apply embed_pref.
Qed.

(* The reverse direction doesn't hold *)

(*********************************************************)
(* Criterium for Liveness Properties Preservation        *)
(*********************************************************)

(* Robust liveness compilation criterium *)
Definition RLC : Prop :=
  forall P C' t, inf t ->
     (exists C, sem tgt ( C' [ P ↓ ]) t ->
           sem src ( C [ P ]) t).

(* the same as for RC *)
Lemma RLC' : RLC <-> (forall P C' t, inf t -> sem tgt ( C' [ P ↓ ]) t ->
                                  exists C,  sem src ( C [ P ]) t).
Proof.
   unfold RLC. split.
  - intros rc P C' t Hi H0. destruct (rc P C' t) as [C H1]. clear rc.
    assumption. exists C. apply (H1 H0).
  - intros rc' P C' t Hi.
    assert (K :  sem tgt ( C' [ P ↓ ]) t \/ ~  sem tgt ( C' [ P ↓ ]) t)
      by now apply classic.
    destruct K as [k | k].
    + destruct (rc' P C' t Hi k) as [C H]. clear rc'.
      exists C. auto.
    + exists some_ctx. intros H. exfalso. apply (k H).
Qed.

Theorem RLC_RLP : RLC <-> (forall P π, Liveness π -> RP P π).
Proof.
  rewrite RLC'. split.
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
    it's the same as all Properties Preservation         *)
(*********************************************************)


(* CA: this condition is trace equality 
       if one of the two traces is finite then 
       also the other one is finite. 
 *)
Lemma rewriting_lemma : forall t1 t2,
    (forall m, prefix m t1 -> prefix m t2) ->
    (forall π, π t1 -> π t2).
Admitted.

Theorem RobsP_RPP : (forall P π, Observable π -> RP P π) <->
                    (forall P π, RP P π).
Proof.
  split; try now firstorder.
  intros hr P π. rewrite contra_RP.
  intros [C' [t [hsem ht]]].
  specialize (hr P (fun b => exists m, prefix m b /\ ~ prefix m t)). 
  assert (Observable (fun b => exists m, prefix m b /\ ~ prefix m t)).
  { unfold Observable. intros t0 [m [h1 h2]].
    exists m. split; try now auto.
    intros t' h'. now exists m. }
  rewrite contra_RP in hr. destruct (hr H) as [C [t' [k1 k2]]]; clear H. 
  exists C',t. split; try now auto. intros [m [hc1 hc2]]. now auto. 
  exists C, t'. split; try now auto.
  intros ff. apply ht.
  apply (rewriting_lemma t' t). intros m hm.
  rewrite not_ex_forall_not in k2. specialize (k2 m). rewrite <- not_imp in k2.
  apply NNPP in k2. now auto. assumption.
Qed. 

Theorem RobsP_RC : (forall P π, Observable π -> RP P π) <-> RC.
Proof. now rewrite RobsP_RPP, RC_RPP. Qed. 

(******************************************************************************)

(** *hyperproperty free criteria *)

Require Import FunctionalExtensionality.
Require Import Logic.ClassicalFacts.


(*********************************************************)
(* Criterium for all HyperProperties Preservation        *)
(*********************************************************)
Definition HRC : Prop :=
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


Theorem HRC_RHP : HRC <-> forall P H, RHP P H.
Proof.
  split.
  - intros H0 P H. rewrite contra_RHP. intros [C' H1].
    specialize (H0 P C'). destruct H0 as [C H0].
    exists C. intros ff. eapply Hequiv_lemma in ff.
    apply (H1 ff). now auto.
  - unfold HRC. intros hrp P C'.
    specialize (hrp P (fun π => π <>  (sem tgt ( C' [ P ↓ ])))).
    rewrite contra_RHP in hrp. destruct hrp as [C H0].
    exists C'. rewrite <- dne. now auto.
    rewrite <- dne in H0. exists C. intros t.
    now  rewrite <- H0. 
Qed.

(*********************************************************)
(* Criterium for SSC HyperProperties Preservation        *)
(*********************************************************)

Definition ssc_cr : Prop :=
  forall P C', 
  exists C, forall b,  sem tgt ( C' [ P ↓ ]) b ->  sem src ( C [ P ]) b.

Lemma SSC_criterium :
  (forall P H, SSC H -> RHP P H) <-> ssc_cr.
Proof.
  split.
  - unfold ssc_cr. intros h0 P C'.
    assert  (s : SSC (fun π => ~(forall b,  sem tgt ( C' [ P ↓ ]) b -> π b))).
    { unfold SSC. intros π h1 k Hk ff.
      assert (foo : forall b,  sem tgt ( C' [ P ↓ ]) b -> π b) by now auto.
      now apply (h1 foo). }   
    specialize (h0 P (fun π => ~(forall b,  sem tgt ( C' [ P ↓ ]) b -> π b)) s).
    rewrite contra_RHP in h0.
    destruct h0 as [C h1]. exists C'. 
    now rewrite <- dne. rewrite <- dne in h1.
    now exists C.
  - intros ssc P H HH. rewrite contra_RHP. intros [C' H0].
    destruct (ssc P C') as [C h0]. exists C. now firstorder.
Qed.


(*********************************************************)
(* Criterium for HyperSafety Preservation                *)
(*********************************************************)

Definition HSRC : Prop :=
  forall P C' M, Observations M ->
            spref M (sem tgt ( C' [ P ↓ ]))  ->
            exists C, spref M (sem src ( C [ P])).

Theorem RHSP_HSRC : (forall P H, HSafe H -> RHP P H) <-> HSRC.
Proof.
  split.
  - unfold HSRC. intros h P C' M h0 h1.
    assert (hs : HSafe (fun π => ~ spref M π)).
    { unfold HSafe. intros T hm. rewrite <- dne in hm.
      exists M. split; now auto. }
    specialize (h P (fun π => ~ spref M π) hs). rewrite contra_RHP in h.
    destruct h as [C hh]. now exists C'. exists C. now apply NNPP. 
  - intros hsrc P H hs. rewrite contra_RHP. intros [C' h0].
    destruct (hs (fun b : trace => sem tgt ( C' [ P ↓ ]) b)) as [M [hm0 [hm1 hm2]]].
    assumption. destruct (hsrc P C' M) as [C hh]; auto. 
    exists C. now apply hm2.
Qed.


(*********************************************************)
(* Criterium for HyperLiveness Preservation      
   is the same as the one for 
   all Hyperproperties Preservation                      *)
(*********************************************************)

Definition Embedding (M : finpref -> Prop) : prop :=
  fun t => exists m, M m /\ t = embedding m.

Lemma infinite_trace_not_in_embed : forall M, ~ (Embedding M) (constant_trace an_event).
Proof.
  intros M hf. inversion hf. destruct H as [h1 h2].
  assert (inf (constant_trace an_event)) by now apply inf_constant_trace.
  assert (fin (embedding x)) by now apply embed_fin.
  rewrite <- h2 in H0.  now apply (H H0).
Qed.  

Lemma bad_HyperLiv : forall C' P,
    HLiv (fun π : prop => π <> (sem tgt ( C' [ P ↓ ] ))).
Proof.
  unfold HLiv. intros C' P M obsM.
  assert (sem tgt (C' [P ↓]) = Embedding M \/  sem tgt (C' [P ↓]) <> Embedding M)
    by now apply classic.
  destruct H.
  + rewrite H; clear H. exists (fun t => (exists m, M m /\ t = embedding m) \/ t = constant_trace an_event).
    split.
    ++ unfold spref. intros m hm. exists (embedding m).
       split.
       +++ left. now exists m. 
       +++ now apply embed_pref.
     ++ intros hf. apply (infinite_trace_not_in_embed M). 
        rewrite <- hf. now right.
  + exists (Embedding M). split; try now auto.
    unfold spref, Embedding. intros m hm.
    exists (embedding m). split.
    ++ now exists m.
    ++ now apply embed_pref. 
Qed. 

Theorem RHLP_RHP : 
    (forall P H, HLiv H -> RHP P H) <-> (forall P H, RHP P H).
Proof.
 split; try now firstorder.
 intros rhlp P H. rewrite contra_RHP. intros [C' K].
 specialize (rhlp P (fun π : prop => π <> sem tgt (C' [ P ↓]) ) (bad_HyperLiv C' P)).
 rewrite contra_RHP in rhlp.
 destruct rhlp as [C KK]. exists C'. now rewrite <- dne. apply NNPP in KK.
 exists C. now rewrite KK.
Qed.

Theorem RHLP_HRC : 
    (forall P H, HLiv H -> RHP P H) <-> HRC.
Proof. now rewrite (RHLP_RHP), (HRC_RHP). Qed.


(*************************************************************************)
(** *Relational                                                          *)
(*************************************************************************)

Definition r2RC := forall Ct P1 P2 t1 t2,
  sem tgt (Ct [P1 ↓]) t1 ->
  sem tgt (Ct [P2 ↓]) t2 ->
  exists Cs, sem src (Cs [P1]) t1 /\ sem src (Cs [P2]) t2.

Lemma r2RPP_r2RC : r2RPP <-> r2RC.
Proof.
  rewrite r2RPP'. unfold r2RPP, r2RC. split.
  - intros H Ct P1 P2 t1 t2 H1 H2.
    specialize (H P1 P2 (fun t1' t2' => t1' <> t1 \/ t2' <> t2)).
    assert(Htriv: ~ (t1 <> t1 \/ t2 <> t2)) by tauto.
    simpl in H. specialize (H Ct t1 t2 H1 H2 Htriv).
    destruct H as [Cs [t1' [t2' [H1' [H2' Heq]]]]].
    exists Cs. rewrite de_morgan2 in Heq. destruct Heq as [Heq1 Heq2].
    apply NNPP in Heq1. apply NNPP in Heq2. subst. tauto.
  - intros H P1 P2 r Ct t1 t2 H1 H2 Hr.
    specialize (H Ct P1 P2 t1 t2 H1 H2).
    destruct H as [Cs [G1 G2]]. now exists Cs, t1, t2.
Qed.

(* Robust Preservation of relations over properties =>
   Robust Property Preservation 
*)
Lemma r2RPP_RPP : r2RPP -> forall P π, RP P π.
Proof.
  unfold r2RPP, RP, rsat, rsat2, sat, sat2.
  intros H P π Hpi Ct t H'. specialize (H P P (fun t1 _ => π t1)).
  simpl in H.
  assert(Hpi1 : forall C t1 t2 ,
                 sem src (C [P]) t1 -> sem src (C [P]) t2 -> π t1) by eauto.
  specialize (H Hpi1 Ct t t). tauto.
Qed.

(*************************************************************************)
(* Robust 2-rel Safety Pres              *)
(* We give three equivalent caracterization of the same criterion: r2RSP, r2RSC
   and two_rRSC *)
(*************************************************************************)
Definition safety2 r := forall (t1 t2 : trace),
    ~ (r t1 t2) ->
    exists (m1 m2 : finpref), prefix m1 t1 /\ prefix m2 t2 /\
                         (forall (t1' t2' : trace), prefix m1 t1' -> prefix m2 t2' -> ~(r t1' t2')).

Definition r2RSP := forall P1 P2 r,
    safety2 r ->
    rsat2 P1 P2 r ->
    rsat2 (P1 ↓) (P2 ↓) r.


Lemma r2RSP' : r2RSP <-> (forall P1 P2 r,
                           safety2 r ->
                           forall Ct t1 t2, sem _ (plug _ (P1 ↓) Ct) t1 ->
                                       sem _ (plug _ (P2 ↓) Ct) t2 -> ~(r t1 t2) ->
                                       exists Cs t1' t2', sem _ (plug _ P1 Cs) t1' /\
                                                     sem _ (plug _ P2 Cs) t2' /\ ~(r t1' t2')).
Proof.
  unfold r2RSP, rsat2, sat2. split.
  - intros H P1 P2 r Hsafety Ct t1 t2 H0 H1 H2. specialize (H P1 P2 r Hsafety).
    rewrite imp_equiv in H. destruct H as [H | H].
    + rewrite not_forall_ex_not in H. destruct H as [Cs H].
      rewrite not_forall_ex_not in H. destruct H as [tt1 H].
      rewrite not_forall_ex_not in H. destruct H as [tt2 H].
      rewrite not_imp in H. destruct H as [k1 k2].
      rewrite not_imp in k2. destruct k2 as [k2 k3].
      now exists Cs, tt1, tt2.
    + exfalso. now apply (H2 (H Ct t1 t2 H0 H1)).
  - intros H P1 P2 r Hsafety H0 C t1 t2 H1 H2. apply NNPP. intros ff.
    specialize (H P1 P2 r Hsafety C t1 t2 H1 H2 ff); destruct H as [Cs [tt1 [tt2 [h0 [h1 h2]]]]].
    now apply (h2 (H0 Cs tt1 tt2 h0 h1)).
Qed.

Definition r2RSC := forall Ct P1 P2 m1 m2,
  psem (plug _ (P1 ↓) Ct) m1 ->
  psem (plug _ (P2 ↓) Ct) m2 ->
  exists Cs, psem (plug _ P1 Cs) m1 /\ psem (plug _ P2 Cs) m2.


Definition two_rRSC : Prop :=
  forall P1 P2 (r : finpref -> finpref -> Prop),
    ((forall Cs m1 m2, psem (Cs [P1]) m1 ->
                  psem (Cs [P2]) m2 ->
                  r m1 m2) ->
     (forall Ct m1 m2, psem (Ct [P1 ↓]) m1 ->
                  psem (Ct [P2 ↓]) m2 ->
                  r m1 m2)).


Theorem r2RSP_r2RSC : r2RSP <-> r2RSC.
Proof.
  rewrite r2RSP'.
  unfold r2RSP, r2RSC. split.  
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
Qed.

Theorem r2RSC_two_rRSC : r2RSC <-> two_rRSC.
Proof.
  unfold r2RSC, two_rRSC.
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


(*************************************************************************)
(* Robust 2-rel HyperProperty Pres => trace equivalence pres             *)
(*************************************************************************)

Definition r2HRP : Prop :=
  forall P1 P2 r, (hrsat2 P1 P2 r) -> (hrsat2 (P1 ↓) (P2 ↓) r).

Lemma r2HRP_teq : r2HRP -> teq_preservation.
Proof.
  unfold r2HRP, hrsat2, hsat2, teq_preservation. intros Hr P1 P2 Hsrc Ct t.
  specialize (Hr P1 P2 (fun π1 π2 => forall t,  π1 t <-> π2 t)).
  simpl in Hr. specialize (Hr Hsrc). now apply (Hr Ct t).
Qed.

(** *TODO: Criterium?*)

(*************************************************************************)
(* If the source language is deterministic than
    r2RC =>  trace equivalence preservation                          *)
(*************************************************************************)


Section source_determinism.

  Hypothesis src_det : forall P t1 t2, sem src P t1 -> sem src P t2 -> t1 = t2.

  Theorem two_RC_teq_preservation : r2RC -> teq_preservation.
  Proof.
    unfold r2RC. rewrite teq'. intros H P1 P2 [Ct [t' H']].   
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

  Theorem r2RPP_teq_preservation : r2RPP -> teq_preservation.
  Proof.
    rewrite r2RPP_r2RC. now apply two_RC_teq_preservation.
  Qed. 
  
End source_determinism.



(*************************************************************************)
(* Robust Relational Hyperproperty Preservation                          *)
(*************************************************************************)

(** *Robust Relational Hyperproperty Preservation*)
Definition rRHP : Prop :=
  forall R : (par src  ->  prop) -> Prop, 
    (forall Cs, R (fun P  => sem src (Cs [ P] ) )) ->
    (forall Ct, R (fun P  => sem tgt (Ct [ (P ↓)]) )). 

(** *Relational Hyperproperty Robust Compilation *)
Definition rRHC : Prop :=
  forall Ct, exists Cs,  (forall P, sem src (Cs [P]) = sem tgt (Ct [P ↓])).

Theorem rRHP_rRHC : rRHP <-> rRHC.
Proof.
  unfold rRHP, rRHC. split.
  - intros hrrhp Ct. apply NNPP. intros ff.
    rewrite not_ex_forall_not in ff.  
    specialize (hrrhp (fun f => exists Cs, forall P, f P = sem src (Cs [ P ]) )). 
    simpl in *. 
    assert (hh : (forall Cs, exists Cs0, forall P, sem src (Cs [P]) = sem src (Cs0 [ P ]))).    
    { intros Cs. now exists Cs. }   
    specialize (hrrhp hh); clear hh.  
    destruct (hrrhp Ct) as [Cs h]. 
    specialize (ff Cs). now apply ff.        
  - intros h R hcs Ct. destruct (h Ct) as [Cs h0]; clear h.
    specialize (hcs Cs).
    assert (hh :  (fun P : par src => sem src (Cs [P])) =
                  (fun P : par src => sem tgt (Ct [P ↓])) ).
    { apply functional_extensionality.
      intros P. specialize (h0 P). now auto. }
    now rewrite <- hh.
Qed.

(*************************************************************************)
(* Robust Relational Safety Preservation                                 *)
(*************************************************************************)

(** *Robust Relational Safety Preservation*)
Definition rRSP : Prop :=
  forall R : (par src -> (finpref -> Prop)) -> Prop,
     (forall Cs f, (forall P, spref (f P) (sem src (Cs [P]))) -> R f) ->
     (forall Ct f, (forall P, spref (f P) (sem tgt (Ct [P↓]))) -> R f).

(** *Relational Safety Robust Compilation *)
Definition rRSC : Prop :=
  forall Ct (f : par src -> (finpref -> Prop)), 
   (forall P, spref (f P) (sem tgt (Ct [P↓]))) ->
   exists Cs,
     (forall P, spref (f P) (sem src (Cs [P]))).

Theorem rRSP_rRSC : rRSP <-> rRSC.
Proof.
  unfold rRSP, rRSC. split.
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
  - intros h R h0 Ct f h1. specialize (h Ct f h1).
    destruct h as [Cs h]. now apply (h0 Cs f h).
Qed.




  

    
    
