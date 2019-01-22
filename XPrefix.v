Require Import Events.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.
Require Import TraceModel.

Variant xpref : Set :=
| xstop   (l : list event) (e : endstate) : xpref
| xtbd    (l : list event)                : xpref
| xsilent (l : list event)                : xpref. 


(** Prefix relation between extended prefixes and traces *)

Definition xprefix (x : xpref) (t : trace) : Prop :=
 match x, t with
 | xstop   lx ex, tstop lt et => ex = et /\ lx = lt
 | xsilent lx   , tsilent lt   => lx = lt
 | xtbd    lx   , tstop lt et => list_list_prefix lx lt
 | xtbd    lx   , tsilent lt  => list_list_prefix lx lt
 | xtbd    lx   , tstream s   => list_stream_prefix lx s
 | _, _ => False
 end. 


Definition xembed (m:finpref) : xpref :=
  match m with
  | fstop l f => xstop l f
  | ftbd  l   => xtbd l
  end.

(* Lemma xsilent_prefix_ftbd_prefix : forall p t, *)
(*   xsilent_prefix p t -> ftbd_prefix p t. *)
(* Proof. *)
(*   induction p; destruct t; simpl; try tauto. intros [H1 H2]. subst a. eauto. *)
(* Qed. *)

Lemma prefix_xprefix_xembed : forall m t, prefix m t -> xprefix (xembed m) t.
Proof. intros [] []; auto.  Qed.

Lemma xprefix_xembed_prefix : forall m t, xprefix (xembed m) t -> prefix m t.
Proof. intros [] []; auto.  Qed.

(* Also definitions corresponding to CommonST *)

Require Import CommonST.

Definition xsem {K : language}
                (P : prg K)
                (m : xpref) : Prop :=
  exists t, xprefix m t /\ (sem K) P t.
