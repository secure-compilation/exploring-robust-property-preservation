Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.
Require Import FunctionalExtensionality.

(** This file defines the robust preservation of several
    classes of properties *)

(** *Robust Preservation of π *)
Definition RP (P : par src) (π : prop) : Prop :=
  rsat P π -> rsat (P ↓) π.

Lemma contra_RP (P : par src) (π : prop) :
     RP P π <->
     ((exists C' t', sem tgt (C' [ P ↓ ]) t'  /\ ~ π t') ->
      (exists C t ,  sem src (C [ P ]) t /\ ~ π t)).
Proof.
   unfold RP. split.
  - intros H. rewrite contra in H.
    repeat rewrite neg_rsat in H. assumption.
  - intros H. rewrite contra.
    repeat rewrite neg_rsat. assumption.
Qed.

(** *RObust Preservation of a class of properties*)
Definition RclassP (class : prop -> Prop) (P : par src) (π : prop) : Prop :=
  class π -> RP P π.

(* RP can be regarded as a monotonic function *)
Lemma RP_monotonic : forall (X Y : prop -> Prop),
    (forall π, Y π -> X π) -> ((forall P π, RclassP X P π) -> (forall P π, RclassP Y P π)).
Proof. unfold RclassP. intros X Y H H0 π P H1. now auto. Qed.

(* big enough classes for RPP *)
Lemma RclassP_sufficient_to_RPP :
  forall (X : prop -> Prop),
    (forall t, X (fun b => b <> t)) -> ((forall P π, RclassP X P π) -> (forall P π, RP P π)).
Proof.
  intros X Hx Hrxp P π. rewrite contra_RP.
  intros [C' [t [H0 H1]]]. specialize (Hrxp P (fun b => b <> t)).
  unfold RclassP in Hrxp. specialize (Hrxp (Hx t)).
  rewrite contra_RP in Hrxp.
  destruct Hrxp as [C [t' [K0 K1]]]; try now exists C', t.
  exists C, t'. split; try now auto. apply NNPP in K1. now subst.
Qed.


(* RP is not strictly monotonic *)
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
      eapply (RclassP_sufficient_to_RPP (fun π => exists t, (forall b, π b <-> b <> t)));
        try now auto.
      ++ intros t. now exists t.
Qed.

(***********************************************************************************)

(** *Robust Preservation of H: hprop *)

Definition RHP (P : par src) (H : hprop) : Prop :=
  rhsat P H -> rhsat (P ↓) H.

Lemma contra_RHP (P : par src) (H : hprop) :
      RHP P H <->
      ((exists C' : ctx tgt, ~ H (beh (C' [ P ↓ ]))) ->
       (exists C  : ctx src, ~ H (beh (C [ P ])))).
Proof.
  unfold RHP, rhsat, hsat. split.
  + intros Hr [C' Hc']. rewrite contra in Hr.
    repeat rewrite not_forall_ex_not in Hr.
    destruct Hr as [C Hc]; try now exists C'. now exists C.
  + intros Himp. rewrite contra. repeat rewrite not_forall_ex_not.
    now auto.
Qed.

(** *Robust Preservation of a class of HyperProperties*)
Definition RHclassP (class : hprop -> Prop) (P : par src) (H : hprop) : Prop :=
  class H -> RHP P H.

Lemma RHP_monotonic : forall (X Y : hprop -> Prop),
    (forall H, Y H -> X H) -> ((forall P H, RHclassP X P H) -> (forall P H, RHclassP Y P H)).
Proof. unfold RclassP. intros X Y H H0 P h H1.
       specialize (H0 P h). unfold RHclassP in *.
       apply H0. firstorder.
Qed.

Lemma RHclassP_sufficient_to_RHP :
  forall (X : hprop -> Prop),
    (forall π, X (fun π' => π' <> π)) -> ((forall P H, RHclassP X P H) -> (forall P H, RHP P H)).
Proof.
  intros X Hx Hrxp P H. rewrite contra_RHP.
  intros [C' Hc']. specialize (Hrxp P (fun μ => μ <> (beh (C' [ P ↓] )))).
  unfold RHclassP in Hrxp. specialize (Hrxp (Hx (beh (C' [ P ↓] )))).
  rewrite contra_RHP in Hrxp.
  destruct Hrxp as [C Hdif]; try now exists C'.
  apply NNPP in Hdif. exists C. now rewrite Hdif.
Qed.

Definition class_lift (H : prop -> Prop) : hprop -> Prop :=
  fun (h : hprop) => exists π, H π /\ h = lifting π.

(* RXP <=> R[X]P *)
Lemma robust_lift_lemma : forall (prop_class : prop -> Prop),
    (forall P π, prop_class π -> RP P π) <->
    (forall P h, (class_lift prop_class) h -> RHP P h).
Proof.
  intros class. unfold RP, rhsat, rsat, hsat, sat. split.
  + intros Hrp P h [π [Hclass Heq]] Hpremise Ct.
    specialize (Hrp P π Hclass). unfold lifting, "<<" in *.
     rewrite Heq in *.
    now firstorder.
  + intros Hrp P π Hclass premise.
    assert (class_lift class (lifting π)) by now exists π.
    specialize (Hrp P (lifting π) H).
    unfold RHP, rhsat, hsat, lifting, "<<" in *.
    now firstorder.
Qed.

(* Robust Preservation of SSC => RPP *)
Lemma RSSCP_RPP : (forall P H, SSC H -> RHP P H) -> (forall P π, RP P π).
Proof.
  assert ((forall P π, RP P π) <-> (forall P π, (fun _ => True) π -> RP P π)) by firstorder.
  rewrite H. rewrite robust_lift_lemma. intros Hssc P h [π [foo Heq]].
  assert (SSC h).
  { apply SSC_iff. exists (fun μ => (forall t, μ t <-> π t)).
    intros μ. rewrite Heq. unfold lifting, "<<" in *.
    now firstorder. }
  now apply Hssc.
Qed.

(** *Relational *)

Definition r2RPP : Prop :=  forall P1 P2 (r : rel_prop),
    rsat2 P1 P2 r -> rsat2 (P1 ↓) (P2 ↓) r .

Lemma r2RPP' :
  r2RPP <->
  (forall P1 P2 r,
  forall Ct t1 t2, sem tgt ( Ct [P1 ↓] )  t1 ->
              sem tgt ( Ct [P2 ↓] )  t2 ->
               ~ (r t1 t2) ->
  exists Cs t1' t2', sem src (Cs [ P1 ]) t1' /\
                sem src (Cs [ P2 ]) t2' /\ ~ (r t1' t2')).
Proof.
  unfold r2RPP, rsat2, sat2. split.
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


Definition teq_preservation : Prop :=
  forall P1 P2, (forall Cs t, sem src (Cs [P1]) t <-> sem src (Cs [P2]) t) ->
           (forall Ct t, sem tgt (Ct [P1 ↓]) t <-> sem tgt (Ct [P2 ↓]) t).

Definition rtip : Prop :=
  forall P1 P2, (forall Cs t, sem src (Cs [P1]) t -> sem src (Cs [P2]) t) ->
           (forall Ct t, sem tgt (Ct [P1 ↓]) t -> sem tgt (Ct [P2 ↓]) t).

Lemma rtip_rtep : rtip -> teq_preservation.
Proof.
  unfold rtip. intros Hrtip P1 P2 H Ct t.
  split; intro H'.
  - eapply Hrtip. Focus 2. eassumption. intros Cs t0 H0.
    apply H. assumption.
  - eapply Hrtip. Focus 2. eassumption. intros Cs t0 H0.
    apply H. assumption.
Qed.

Lemma teq' : teq_preservation <-> (forall P1 P2,
 (exists Ct t, ~ (sem tgt (Ct [P1 ↓]) t  <-> sem tgt (Ct [P2 ↓]) t)) ->
 (exists Cs t', ~ (sem src (Cs [P1]) t'  <-> sem src (Cs [P2]) t'))).
Proof.
  unfold teq_preservation. split.
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
