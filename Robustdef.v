Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.

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
  forall π, class π -> RP P π.


(* Bookmark: line 351, TraceFiniInf.v*)