Require Import Events.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.
Require Import TraceModel.

Inductive xpref : Set :=
| xstop : pref -> endstate -> xpref
| xtbd  : pref -> xpref
| xsilent : pref -> xpref.

(** Prefix relation between extended prefixes and traces *)

Fixpoint xsilent_prefix (m : pref) (t : trace) : Prop :=
  match m, t with
    | nil, tsilent => True
    | nil, _        => False
    | cons e1 m', tcons e2 t' => e1 = e2 /\ xsilent_prefix m' t'
    | _, _          => False
  end.

Definition xprefix (m : xpref) (t : trace) : Prop :=
  match m with
  | xstop m f => fstop_prefix m f t
  | xtbd m  => ftbd_prefix m t
  | xsilent m => xsilent_prefix m t
  end.

Definition xembed (m:finpref) : xpref :=
  match m with
  | fstop m f => xstop m f
  | ftbd m  => xtbd m
  end.

Lemma xsilent_prefix_ftbd_prefix : forall p t,
  xsilent_prefix p t -> ftbd_prefix p t.
Proof.
  induction p; destruct t; simpl; try tauto. intros [H1 H2]. subst a. eauto.
Qed.

Lemma prefix_xprefix_xembed : forall m t, prefix m t -> xprefix (xembed m) t.
Proof. intros m t H. destruct m; simpl in *; assumption. Qed.

Lemma xprefix_xembed_prefix : forall m t, xprefix (xembed m) t -> prefix m t.
Proof. intros m t H. destruct m; simpl in *; assumption. Qed.

(* Also definitions corresponding to CommonST *)

Require Import CommonST.

Definition xsem {K : language}
                (P : prg K)
                (m : xpref) : Prop :=
  exists t, xprefix m t /\ (sem K) P t.
