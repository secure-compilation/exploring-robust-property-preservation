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


Definition xpr (x1 x2 : xpref) :=
  match x1, x2 with
  | xtbd l1, xtbd l2 => list_list_prefix l1 l2
  | xtbd l1, xstop l2 e2 => list_list_prefix l1 l2
  | xtbd l1, xsilent l2  => list_list_prefix l1 l2
  | xstop l1 e1, xstop l2 e2 => e1 = e2 /\ l1 = l2
  | xsilent l1, xsilent l2 => l1 = l2
  | _, _ => False
  end.

Lemma xsame_ext : forall x1 x2 t, xprefix x1 t -> xprefix x2 t -> xpr x1 x2 \/ xpr x2 x1.
Proof.
  intros m1 m2 [] Hpref1 Hpref2.
  + destruct m1, m2; simpl in *; try now auto.
    ++ inversion Hpref1; inversion Hpref2; subst; now auto.
    ++ inversion Hpref1; subst; now right.
    ++ inversion Hpref2; subst; now left.
    ++ now apply (list_list_same_ext l0 l1 l).
 + destruct m1, m2; simpl in *; try now auto.
   ++ now apply (list_list_same_ext l0 l1 l).
   ++ subst; now left.
   ++ subst; now right.
   ++ subst; now auto.
 + destruct m1, m2; simpl in *; try now auto.
   ++ now apply (list_stream_same_ext l l0 s).
Qed.
