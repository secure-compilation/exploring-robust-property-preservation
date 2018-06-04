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

