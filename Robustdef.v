Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.
Require Import FunctionalExtensionality.

(** *Robust Preservation of π *)
Definition RP (P : prg src) (π : prop) : Prop :=
  rsat P π -> rsat (P ↓) π.

Lemma contra_RP (P : prg src) (π : prop) :
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
Definition RclassP (class : prop -> Prop) (P : prg src) (π : prop) : Prop :=
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
      intros [t Heq]. destruct t;
      [specialize (Heq (tcons an_event tstop))
      |specialize (Heq tstop)];  now rewrite Heq.    
    + unfold RclassP. intros P π H tt. 
      eapply (RclassP_sufficient_to_RPP (fun π => exists t, (forall b, π b <-> b <> t)));
        try now auto. 
      ++ intros t. now exists t.
Qed.

(***********************************************************************************)

(** *Robust Preservation of H: hprop *)

Definition RHP (P : prg src) (H : hprop) : Prop :=
  rhsat P H -> rhsat (compile P) H.

Lemma contra_RHP (P : prg src) (H : hprop) :
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

(** *RObust Preservation of a class of properties*)
Definition RHclassP (class : hprop -> Prop) (P : prg src) (H : hprop) : Prop :=
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
