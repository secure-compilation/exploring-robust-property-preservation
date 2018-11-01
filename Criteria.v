Require Import ClassicalExtras.
Require Import Setoid.
Require Import Events.
Require Import CommonST.
Require Import TraceModel.
Require Import Robustdef.
Require Import Properties.
Require Import Topology.

(** This file proves the alternative, property-free criteria
    for the robust preservation of classes of properties *)


(*********************************************************)
(* Criterium for all Properties Preservation             *)
(*********************************************************)

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
Theorem RTC_RTP : RTC <-> (forall P π, RP P π).
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
    + exists some_ctx_src. intros H. exfalso. apply (k H).
Qed.

Theorem RDC_RDP : RLC <-> (forall P π, Liveness π -> RP P π).
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

*)

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


Theorem RHC_RHP : HRC <-> forall P H, RHP P H.
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

(* RB: Rename. *)
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

(* 2SC Hyperproperties *)

(* CA : according to this definition
         H ∈ k-SC iff 
         ∃ t1 .. tk, H = lifting (true \ t1) ∪ .. ∪ lifting (true \ tk)

   notice that

   (1) H ∈ 2-SC -> H ∈ k-SC ∀ k >= 2   (just take t3 = .. = tk = t2)
   
   (2) H ∈ 2-SC -> H ∈ SC 
       by a previous characterization of SC hyperproperties.

   ------------------------------------------------------------------------------

   for k -> ∞ 

    H ∈ lim_{k -> ∞ } k -SC iff
    H = ∪_{t : trace} lifting (true \ t) = prop \ {t | t : trace}

   Consequences : 
   ---------------

   (i)   such a limit is not the class SSC (and it contains only one hyperproperty)

   (ii)  H ∈ 2-SC does not imply H ∈ lim_{k -> ∞ } k -SC   

         e.g. lifting (true \ t) for a fixed t is in 2-SC (as ∃ t, t ..)
              
               but it is different from 
               prop \ {t | t : trace} (the only inhabitant of lim_{k -> ∞ } k -SC)


 CA: anycase nothing changes in the diagram, 
     see theorem  R2SCHP_R2HSP 
     
 *)

Definition twoSC (H : hprop) : Prop :=
  exists t1 t2, forall b, ~ (H b) <->  (b t1 /\ b t2).

Definition R2SCHC :=
  forall P Ct t1 t2,
      (sem tgt (Ct [P ↓]) t1 /\ sem tgt (Ct [P ↓]) t2)
      -> exists Cs, (sem src (Cs [P ]) t1 /\ sem src (Cs [P ]) t2).

(* RB: This also inverts the usual order of the pair. *)
Theorem R2SCHP_R2SCHC :
  (forall P H, twoSC H -> RHP P H) <-> R2SCHC.
Proof.
  split.
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
  - intros ssc P H HH. rewrite contra_RHP. intros [C' H0].
    specialize (ssc P C'). unfold twoSC in HH. destruct HH as [t1 [t2 HH]].
    specialize (ssc t1 t2). destruct ssc as [C h0].
    split; firstorder.
    exists C. firstorder.
Qed.



(*********************************************************)
(* Criterium for HyperSafety Preservation                *)
(*********************************************************)

Definition RHSC : Prop :=
  forall P C' M, Observations M ->
            spref M (sem tgt ( C' [ P ↓ ]))  ->
            exists C, spref M (sem src ( C [ P])).

(* RB: Most previous results invert the order of the terms. *)
Theorem RHSP_RHSC : (forall P H, HSafe H -> RHP P H) <-> RHSC.
Proof.
  split.
  - unfold RHSC. intros h P C' M h0 h1.
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

(* 2-Hypersafety *)
Definition H2Safe (H : hprop) : Prop :=
  forall (b : prop), ~ (H b) ->
                (exists (m1 m2 : finpref),
                    spref (fun m => m = m1 \/ m = m2) b /\
                    forall b', spref (fun m => m = m1 \/ m = m2) b' -> ~(H b')).

Definition R2HSC := forall P Ct, forall m1 m2,
        (spref (fun m => m = m1 \/ m = m2) (sem tgt ( Ct [ P ↓]))
         -> exists Cs, spref (fun m => m = m1 \/ m = m2) (sem src ( Cs [ P]))).

Theorem R2HSP_R2HSC : (forall P H, H2Safe H -> RHP P H) <-> R2HSC.
Proof.
  split.
  - unfold R2HSC.
    intros. specialize (H P).
    assert (hs : H2Safe (fun π => ~ spref (fun m => m = m1 \/ m = m2) π)).
    { clear. unfold H2Safe. intros b hm. rewrite <- dne in hm.
      exists m1, m2. split. assumption. now auto. }
    specialize (H (fun π => ~ spref (fun m => m = m1 \/ m = m2) π) hs).
    rewrite contra_RHP in H. destruct H as [C hh].
    now exists Ct. exists C. now apply NNPP.
  - intros hsrc P H hs. rewrite contra_RHP. intros [C' h0].
    destruct (hs (fun b => sem tgt (C' [P ↓]) b)) as [m1 [m2 [H1 H2]]].
    assumption.
    destruct (hsrc P C' m1 m2) as [C hh]; auto.
    exists C. now apply H2.
Qed.

Lemma R2HSP_RSP : R2HSC -> RSC. 
Proof.
  intros H P Ct t Ht m Hpref.
  destruct (H P Ct m m) as [Cs Hspref].
  intros m' [K | K]; subst; now exists t.
  exists Cs. destruct (Hspref m) as [t' H']; auto.
Qed.


Lemma R2SCHP_R2HSP : (forall P H, twoSC H -> RHP P H) -> (forall P H, H2Safe H -> RHP P H).
Proof.
  rewrite  R2SCHP_R2SCHC, R2HSP_R2HSC. 
  intros rsc P Ct m1 m2 H. unfold spref in *.
  destruct (H m1) as [t1 [Ht1 Hpref1]]; auto.   
  destruct (H m2) as [t2 [Ht2 Hpref2]]; auto.
  specialize (rsc P Ct t1 t2). destruct rsc as [Cs [K1 K2]]; auto.
  exists Cs. intros x [H1 | H2]; subst; [now exists t1 | now exists t2].
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
Proof. now rewrite (RHLP_RHP), (RHC_RHP). Qed.


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
(* We give three equivalent caracterization of the same criterion: R2rSP, R2rSC
   and R2rSC' *)
(*************************************************************************)
Definition safety2 r := forall (t1 t2 : trace),
    ~ (r t1 t2) ->
    exists (m1 m2 : finpref), prefix m1 t1 /\ prefix m2 t2 /\
                         (forall (t1' t2' : trace), prefix m1 t1' -> prefix m2 t2' -> ~(r t1' t2')).

Definition R2rSP := forall P1 P2 r,
    safety2 r ->
    rsat2 P1 P2 r ->
    rsat2 (P1 ↓) (P2 ↓) r.


Lemma R2rSP' : R2rSP <-> (forall P1 P2 r,
                           safety2 r ->
                           forall Ct t1 t2, sem _ (plug _ (P1 ↓) Ct) t1 ->
                                       sem _ (plug _ (P2 ↓) Ct) t2 -> ~(r t1 t2) ->
                                       exists Cs t1' t2', sem _ (plug _ P1 Cs) t1' /\
                                                     sem _ (plug _ P2 Cs) t2' /\ ~(r t1' t2')).
Proof.
  unfold R2rSP, rsat2, sat2. split.
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

Definition R2rSC := forall Ct P1 P2 m1 m2,
  psem (plug _ (P1 ↓) Ct) m1 ->
  psem (plug _ (P2 ↓) Ct) m2 ->
  exists Cs, psem (plug _ P1 Cs) m1 /\ psem (plug _ P2 Cs) m2.


Definition R2rSC' : Prop :=
  forall P1 P2 (r : finpref -> finpref -> Prop),
    ((forall Cs m1 m2, psem (Cs [P1]) m1 ->
                  psem (Cs [P2]) m2 ->
                  r m1 m2) ->
     (forall Ct m1 m2, psem (Ct [P1 ↓]) m1 ->
                  psem (Ct [P2 ↓]) m2 ->
                  r m1 m2)).


Theorem R2rSP_R2rSC : R2rSP <-> R2rSC.
Proof.
  rewrite R2rSP'.
  unfold R2rSP, R2rSC. split.
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


Definition alternative := forall P1 P2 S1 S2,
    Safety S1 -> Safety S2 ->
    (exists Ct, ~ sat (Ct [P1 ↓]) S1 /\ ~ sat (Ct [P2 ↓]) S2) ->
    (exists Cs, ~ sat (Cs [P1]) S1 /\ ~ sat (Cs [P2]) S2).

(* aletrnative <->
    forall P1 P2 S1 S2, 
    Safety S1 -> Safety S2 ->  
    (forall Cs, sat (Cs [P1]) S1 \/ sat (Cs[P2]) S2) -> 
    (forall Ct, sat (Ct [P1↓]) S1 \/ sat (Ct[P2↓]) S2)
 *)

Lemma alternative_R2rSC : alternative <-> R2rSC.
Proof.
  split; intros H.
  + intros Ct P1 P2 m1 m2 H1 H2.
    specialize (H P1 P2 (fun t => ~ prefix m1 t) (fun t => ~ prefix m2 t)).
    assert (s1 : Safety  (fun t => ~ prefix m1 t)).
    { intros t Ht. apply NNPP in Ht. now exists m1. }  
    assert (s2 : Safety  (fun t => ~ prefix m2 t)).
    { intros t Ht. apply NNPP in Ht. now exists m2. } 
    specialize (H s1 s2). destruct H as [Cs [Hc1 Hc2]].
    exists Ct. split.
    ++ intros Hs.
       destruct (H1) as [t1 [Hpref Ht1]].
       specialize (Hs t1 Ht1). simpl in Hs. contradiction.   
    ++ intros Hs.
       destruct (H2) as [t2 [Hpref Ht2]].
       specialize (Hs t2 Ht2). simpl in Hs. contradiction.
    ++ exists Cs. split.
       +++ unfold sat in Hc1. rewrite not_forall_ex_not in Hc1.
           destruct Hc1 as [t1 Hc1].
           rewrite not_imp in Hc1. exists t1. 
           destruct Hc1 as [Hc11 Hc12].
           rewrite <- dne in Hc12. now auto. 
       +++ unfold sat in Hc2. rewrite not_forall_ex_not in Hc2.
           destruct Hc2 as [t2 Hc2].
           rewrite not_imp in Hc2. exists t2. 
           destruct Hc2 as [Hc21 Hc22].
           rewrite <- dne in Hc22. now auto.
  + intros P1 P2 S1 S2 HS1 HS2 [Ct [Hc1 Hc2]].
    unfold sat in Hc1,Hc2.
    rewrite not_forall_ex_not in Hc1,Hc2.
    destruct Hc1 as [t1 Hc1]. destruct Hc2 as [t2 Hc2].
    rewrite not_imp in Hc1,Hc2.
    destruct Hc1 as [Hc1 Ht1]. destruct Hc2 as [Hc2 Ht2].
    destruct (HS1 t1 Ht1) as [m1 [Hpref1 H1]].
    destruct (HS2 t2 Ht2) as [m2 [Hpref2 H2]].
    specialize (H Ct P1 P2 m1 m2). destruct H as [Cs [Hpsem1 Hpsem2]].
    ++ now exists t1.
    ++ now exists t2.
    ++ destruct Hpsem1 as [tt1 [Hm1 Hsem1]]. destruct Hpsem2 as [tt2 [Hm2 Hsem2]]. 
       exists Cs. split; unfold sat; rewrite not_forall_ex_not;
               [exists tt1 |exists tt2]; rewrite not_imp; now auto.                 
Qed.

Lemma alternative_R2rSP : alternative <-> R2rSP.
Proof.
 now rewrite R2rSP_R2rSC, alternative_R2rSC.
Qed. 
    
(*************************************************************************)
(* Robust 2-relational Hyperproperty Preservation *)
(*************************************************************************)

Definition R2rHP : Prop :=
  forall P1 P2 r, (hrsat2 P1 P2 r) -> (hrsat2 (P1 ↓) (P2 ↓) r).

Definition R2rHC : Prop :=
  forall P1 P2 Ct, exists Cs, (sem src (Cs [P1]) = sem tgt (Ct [P1 ↓]))
                    /\ (sem src (Cs [P2]) = sem tgt (Ct [P2 ↓])).


Theorem R2rHP_R2rHC : R2rHP <-> R2rHC.
Proof.
  unfold R2rHP, R2rHC; split.
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
  - intros h P1 P2 r hcs Ct. destruct (h P1 P2 Ct) as [Cs [h0 h1]]; clear h.
    specialize (hcs Cs).
    rewrite h0, h1 in hcs. now assumption.
Qed. 

(*************************************************************************)
(* Robust 2-rel HyperProperty Pres => trace equivalence pres             *)
(*************************************************************************)


Lemma R2rHP_teq : R2rHP -> teq_preservation.
Proof.
  unfold R2rHP, hrsat2, hsat2, teq_preservation. intros Hr P1 P2 Hsrc Ct t.
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

  Theorem two_RSC_teq_preservation : r2RC -> teq_preservation.
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

End source_determinism.


(*************************************************************************)
(* Robust Relational Hyperproperty Preservation                          *)
(*************************************************************************)

(** *Robust Relational Hyperproperty Preservation*)
Definition RrHP : Prop :=
  forall R : (par src  ->  prop) -> Prop,
    (forall Cs, R (fun P  => sem src (Cs [ P] ) )) ->
    (forall Ct, R (fun P  => sem tgt (Ct [ (P ↓)]) )).

(** *Relational Hyperproperty Robust Compilation *)
Definition RrHC : Prop :=
  forall Ct, exists Cs,  (forall P, sem src (Cs [P]) = sem tgt (Ct [P ↓])).

Theorem RrHP_RrHC : RrHP <-> RrHC.
Proof.
  unfold RrHP, RrHC. split.
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
Definition RrSP : Prop :=
  forall R : (par src -> (finpref -> Prop)) -> Prop,
     (forall Cs f, (forall P, spref (f P) (sem src (Cs [P]))) -> R f) ->
     (forall Ct f, (forall P, spref (f P) (sem tgt (Ct [P↓]))) -> R f).

(** *Relational Safety Robust Compilation *)
Definition RrSC : Prop :=
  forall Ct (f : par src -> (finpref -> Prop)),
   (forall P, spref (f P) (sem tgt (Ct [P↓]))) ->
   exists Cs,
     (forall P, spref (f P) (sem src (Cs [P]))).

Theorem RrSP_RrSC : RrSP <-> RrSC.
Proof.
  unfold RrSP, RrSC. split.
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
 
(*************************************************************************)
(* Robust Relational Subset Closed                                       *)
(*************************************************************************)

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
