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
