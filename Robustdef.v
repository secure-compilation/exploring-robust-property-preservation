Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.
Require Import XPrefix.


(** This file defines the robust preservation of several
    classes of properties *)

(*********************************************************)
(* PROPERTIES                                            *)
(*********************************************************)

Definition RP (P : par src i) (π : prop) :=
  rsat P π -> rsat (P↓) π.


(** *Robust Preservation of Trace Properties *)
Definition RTP := forall (P : par src i) (π : prop), RP P π.

Lemma contra_RP : forall P π,
     RP P π <->
     ((exists C' t', sem tgt (C' [ P ↓ ]) t'  /\ ~ π t') ->
      (exists C t ,  sem src (C [ P ]) t /\ ~ π t)).
Proof.
  intros P π. unfold RP. split; intros H.
  - rewrite contra in H.
    repeat rewrite neg_rsat in H. auto.
  - rewrite contra. repeat rewrite neg_rsat. auto.
Qed.

(** *RObust Preservation of a class of properties*)
Definition RclassP (class : prop -> Prop) (P : par src i) (π : prop) : Prop :=
  class π -> RP P π.

(* RP can be regarded as a monotonic function *)
Lemma RP_monotonic : forall (X Y : prop -> Prop),
    (forall π, Y π -> X π) -> ((forall P π, RclassP X P π) -> (forall P π, RclassP Y P π)).
Proof. unfold RclassP. intros X Y H H0 π P H1. now auto. Qed.

(* big enough classes for RTP *)
Lemma RclassP_sufficient_to_RTP :
  forall (X : prop -> Prop),
    (forall t, X (fun b => b <> t)) -> ((forall P π, RclassP X P π) -> forall P π, RP P π).
Proof.
  intros X Hx Hrxp P π. rewrite contra_RP.
  intros [C' [t [H0 H1]]]. specialize (Hrxp P (fun b => b <> t)).
  unfold RclassP in Hrxp. specialize (Hrxp (Hx t)).
  rewrite contra_RP in Hrxp.
  destruct Hrxp as [C [t' [K0 K1]]]; try now exists C', t.
  exists C, t'. split; try now auto. apply NNPP in K1. now subst.
Qed.


(* RTP is not strictly monotonic *)
Lemma RclassP_not_strict : exists (X Y : prop -> Prop),
    (forall π, Y π -> X π) /\ (exists π, X π /\ ~ Y π) /\
    ((forall P π, RclassP Y P π) -> (forall P π, RclassP X P π)).
Proof.
    exists (fun π => True), (fun π => exists t, (forall b, π b <-> b <> t)).
    split; try now auto.
    split.
    + exists (fun t => False).  split; auto.
      intros [t Heq].  destruct t.
      ++ now apply (Heq (tsilent l)).
      ++ now apply (Heq (tstop l an_endstate)).
      ++ now apply (Heq (tstop nil an_endstate)).
    + unfold RclassP. intros P π H tt.
      eapply (RclassP_sufficient_to_RTP (fun π => exists t, (forall b, π b <-> b <> t)));
        try now auto.
      ++ intros t. now exists t.
Qed.

(** *Robust Preservation of Safety Properties *)

Definition RSP := forall P π, Safety π -> RP P π.

(** *Robust Preservation of Liveness Properties *)

Definition RDP := forall P π, Dense π -> RP P π.


(*********************************************************)
(*   HYPERPROPERTIES                                     *)
(*********************************************************)

(** *Robust Preservation of H: hprop *)

Definition RhP (P : par src i) (H : hprop) :=
  rhsat P H -> rhsat (P ↓) H.

Definition RHP := forall P H, RhP P H.

Lemma contra_RHP (P : par src i) (H : hprop) :
      RhP P H <->
      ((exists C' : ctx tgt (cint i), ~ H (beh (C' [ P ↓ ]))) ->
       (exists C  : ctx src i, ~ H (beh (C [ P ])))).
Proof.
  unfold RhP, rhsat, hsat. split.
  + intros Hr [C' Hc']. rewrite contra in Hr.
    repeat rewrite not_forall_ex_not in Hr.
    destruct Hr as [C Hc]; try now exists C'. now exists C.
  + intros Himp. rewrite contra. repeat rewrite not_forall_ex_not.
    now auto.
Qed.

(** *Robust Preservation of a class of HyperProperties*)
Definition RHclassP (class : hprop -> Prop) (P : par src i) (H : hprop) : Prop :=
  class H -> RhP P H.

Lemma RHP_monotonic : forall (X Y : hprop -> Prop),
    (forall H, Y H -> X H) -> ((forall P H, RHclassP X P H) -> (forall P H, RHclassP Y P H)).
Proof. unfold RclassP. intros X Y H H0 P h H1.
       specialize (H0 P h). unfold RHclassP in *.
       apply H0. firstorder.
Qed.

Lemma RHclassP_sufficient_to_RHP :
  forall (X : hprop -> Prop),
    (forall π, X (fun π' => π' <> π)) -> ((forall P H, RHclassP X P H) -> (forall P H, RhP P H)).
Proof.
  intros X Hx Hrxp P H. rewrite contra_RHP.
  intros [C' Hc']. specialize (Hrxp P (fun μ => μ <> (beh (C' [ P ↓] )))).
  unfold RHclassP in Hrxp. specialize (Hrxp (Hx (beh (C' [ P ↓] )))).
  rewrite contra_RHP in Hrxp.
  destruct Hrxp as [C Hdif]; try now exists C'.
  apply NNPP in Hdif. exists C. now rewrite Hdif.
Qed.


(* RXP <=> R[X]P *)
Lemma robust_lift_lemma : forall (prop_class : prop -> Prop),
    (forall P π, prop_class π -> RP P π) <->
    (forall P h, (class_lift prop_class) h -> RhP P h).
Proof.
  intros class. unfold RP, rhsat, rsat, hsat, sat. split.
  + intros Hrp P h [π [Hclass Heq]] Hpremise Ct.
    specialize (Hrp P π Hclass). unfold lifting, "⊆" in *.
    rewrite Heq in *.
    now firstorder.
  + intros Hrp P π Hclass premise.
    assert (class_lift class (lifting π)) by now exists π.
    specialize (Hrp P (lifting π) H).
    unfold RhP, rhsat, hsat, lifting, "⊆" in *.
    now firstorder.
Qed.

(** *Robust Preservation of Subset Closed HyperProperties *)


Definition RSCHP := forall P H, SSC H -> RhP P H.

(* Robust Preservation of SSC => RPP *)
Lemma RSSCP_RPP : RSCHP -> RTP.
Proof.
  assert ((forall P π, RP P π) <-> (forall P π, (fun _ => True) π -> RP P π)) by firstorder.
  rewrite H. rewrite robust_lift_lemma. intros Hssc P h [π [foo Heq]].
  assert (SSC h).
  { apply SSC_iff. exists (fun μ => (forall t, μ t <-> π t)).
    intros μ. rewrite Heq. unfold lifting, "⊆" in *.
    now firstorder. }
  now apply Hssc.
Qed.

(** *Robust Preservation of 2-Subset Closed HyperProperties *)

Definition R2SCHP := forall P H, twoSC H -> RhP P H.

(** *Robust Preservation of HyperSafety  *)

Definition RHSP := forall P H, HSafe H -> RhP P H.


(** *Robust Preservation of 2-HyperSafety *)

Definition R2HSP := forall P H, H2Safe H -> RhP P H.

(** *Robust Preservation of HyperLiveness  *)

Definition RHLP := forall P H, HLiv H -> RhP P H.



(*********************************************************)
(*   RELATIONS                                           *)
(*********************************************************)


(** *Robust Preservation of 2-Relational Properties *)

Definition R2rTP : Prop :=  forall (P1 P2 : par src i) (r : rel_prop),
    rsat2 P1 P2 r -> rsat2 (P1 ↓) (P2 ↓) r .

Lemma R2rTP' :
  R2rTP <->
  (forall (P1 P2 : par src i) r,
  forall Ct t1 t2, sem tgt ( Ct [P1 ↓] )  t1 ->
              sem tgt ( Ct [P2 ↓] )  t2 ->
               ~ (r t1 t2) ->
  exists Cs t1' t2', sem src (Cs [ P1 ]) t1' /\
                sem src (Cs [ P2 ]) t2' /\ ~ (r t1' t2')).
Proof.
  unfold R2rTP, rsat2, sat2. split.
  - intros H P1 P2 r Ct t1 t2 H0 H1 H2. specialize (H P1 P2 r).
    rewrite imp_equiv in H. destruct H as [H | H].
    + rewrite not_forall_ex_not in H. destruct H as [Cs H].
      rewrite not_forall_ex_not in H. destruct H as [tt1 H].
      rewrite not_forall_ex_not in H. destruct H as [tt2 H].
      rewrite not_imp in H. destruct H as [k1 k2].
      rewrite not_imp in k2. destruct k2 as [k2 k3].
      now exists Cs, tt1, tt2.
   + exfalso. now apply (H2 (H Ct t1 t2 H0 H1)).
  - intros H P1 P2 r H0 C t1 t2 H1 H2. apply NNPP. intros ff.
    specialize (H P1 P2 r C t1 t2 H1 H2 ff); destruct H as [Cs [tt1 [tt2 [h0 [h1 h2]]]]].
    now apply (h2 (H0 Cs tt1 tt2 h0 h1)).
Qed.

(* Robust Preservation of relations over properties =>
   Robust Property Preservation
*)
Lemma R2rTP_RPP : R2rTP -> RTP.
Proof.
  unfold R2rTP, RTP, RP, rsat, rsat2, sat, sat2.
  intros H P π Hpi Ct t H'. specialize (H P P (fun t1 _ => π t1)).
  simpl in H.
  assert(Hpi1 : forall C t1 t2 ,
                 sem src (C [P]) t1 -> sem src (C [P]) t2 -> π t1) by eauto.
  specialize (H Hpi1 Ct t t). tauto.
Qed.

(** *Robust Preservation of arbitrary-Relational Properties *)


Definition RrTP' : Prop :=
  forall R : (par src i  ->  trace) -> Prop,
    (forall Cs f,  (forall P, sem src (Cs [P]) (f P)) -> R f) ->
    (forall Ct f,  (forall P, sem tgt (Ct [P↓]) (f P)) -> R f).



(** *Robust Preservation of 2-Relational Safety Properties *)

Definition R2rSP := forall (P1 P2 : par src i) r,
    safety2 r ->
    rsat2 P1 P2 r ->
    rsat2 (P1 ↓) (P2 ↓) r.


Lemma R2rSP' : R2rSP <-> (forall (P1 P2 : par src i) r,
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



(** *Robust Preservation of arbitrary Relational Safety Properties*)

Definition RrSP' : Prop :=
  forall R : (par src i -> (finpref -> Prop)) -> Prop,
     (forall Cs f, (forall P, spref (f P) (sem src (Cs [P]))) -> R f) ->
     (forall Ct f, (forall P, spref (f P) (sem tgt (Ct [P↓]))) -> R f).


(** *Robust Preservation of 2-Relational Xafety Properties*)

Definition R2rXP := forall (P1 P2 : par src i) r,
    xafety2 r ->
    rsat2 P1 P2 r ->
    rsat2 (P1 ↓) (P2 ↓) r.

Lemma R2rXP' : R2rXP <-> (forall (P1 P2 : par src i) r,
                           xafety2 r ->
                           forall Ct t1 t2, sem _ (plug _ (P1 ↓) Ct) t1 ->
                                       sem _ (plug _ (P2 ↓) Ct) t2 -> ~(r t1 t2) ->
                                       exists Cs t1' t2', sem _ (plug _ P1 Cs) t1' /\
                                                     sem _ (plug _ P2 Cs) t2' /\ ~(r t1' t2')).
Proof.
  unfold R2rXP, rsat2, sat2. split.
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

(** *Robust Preservation of arbitrary Relational XSafety Properties*)

Definition RrXP' : Prop :=
  forall R : (par src i -> (xpref -> Prop)) -> Prop,
     (forall Cs f, (forall P, spref_x (f P) (sem src (Cs [P]))) -> R f) ->
     (forall Ct f, (forall P, spref_x (f P) (sem tgt (Ct [P↓]))) -> R f).


(** *Robust Preservation of 2-Relational  HyperProperties *)

Definition R2rHP : Prop :=
  forall (P1 P2 : par src i) r, (hrsat2 P1 P2 r) -> (hrsat2 (P1 ↓) (P2 ↓) r).


(** *Robust Preservation of arbitrary Relational HyperProperties*)

Definition RrHP' : Prop :=
  forall R : (par src i  ->  prop) -> Prop,
    (forall Cs, R (fun P  => sem src (Cs [ P] ) )) ->
    (forall Ct, R (fun P  => sem tgt (Ct [ (P ↓)]) )).


(** *Robust Preservation of 2-subsetclosed Relational HyperProperties*)

Definition R2rSCHP := forall (P1 P2 : par src i) r,
    ssc2 r ->
    (hrsat2 P1 P2 r) -> (hrsat2 (P1↓) (P2↓) r).

Lemma R2rSCHP' :
  R2rSCHP <->
  (forall (P1 P2 : par src i) r, ssc2 r ->
                            ((exists Ct, ~ r (beh (Ct [P1↓])) (beh (Ct [P2↓]))) ->
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



(** *Robust Trace Equivalence Preservation *)
Definition RTEP : Prop :=
  forall (P1 P2: par src i),
           (forall Cs t, sem src (Cs [P1]) t <-> sem src (Cs [P2]) t) ->
           (forall Ct t, sem tgt (Ct [P1 ↓]) t <-> sem tgt (Ct [P2 ↓]) t).

Lemma RTEP' : RTEP <-> (forall (P1 P2:par src i),
 (exists Ct t, ~ (sem tgt (Ct [P1 ↓]) t  <-> sem tgt (Ct [P2 ↓]) t)) ->
 (exists Cs t', ~ (sem src (Cs [P1]) t'  <-> sem src (Cs [P2]) t'))).
Proof.
  unfold RTEP. split.
  - intros He P1 P2. specialize (He P1 P2). rewrite imp_equiv in He.
    destruct He as [He | He]; intros [Ct [t Hdiff]].
    + rewrite not_forall_ex_not in He. destruct He as [Cs Hd].
      rewrite not_forall_ex_not in Hd. destruct Hd as [t' Hd].
      now exists Cs,t'.
    + exfalso. apply Hdiff. now apply He.
  - intros H P1 P2 Hsrc Ct t. apply NNPP. intros Hf.
    destruct (H P1 P2) as [Cs [t' Hc]].
    now exists Ct, t. apply Hc. now apply Hsrc.
Qed.

Lemma R2rHP_RTEP : R2rHP -> RTEP.
Proof.
  unfold R2rHP, hrsat2, hsat2, RTEP. intros Hr P1 P2 Hsrc Ct t.
  specialize (Hr P1 P2 (fun π1 π2 => forall t,  π1 t <-> π2 t)).
  simpl in Hr. specialize (Hr Hsrc). now apply (Hr Ct t).
Qed.


(** *Robust Trace Inclusion Preservation *)
Definition RTIP : Prop :=
  forall (P1 P2:par src i),
           (forall Cs t, sem src (Cs [P1]) t -> sem src (Cs [P2]) t) ->
           (forall Ct t, sem tgt (Ct [P1 ↓]) t -> sem tgt (Ct [P2 ↓]) t).

Lemma RTIP_RTEP : RTIP -> RTEP.
Proof.
  unfold RTIP, RTEP.
  intros rtip P1 P2 Hsrc Ct t.
  split; [apply (rtip P1 P2) | apply (rtip P2 P1)]; firstorder.
Qed.
