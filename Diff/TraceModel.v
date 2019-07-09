From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.
Require Import Stream.

Record Events := {

               ev : Type;
               an_ev : ev;
               another_ev : ev;
               different_evs : an_ev <> another_ev;
               eq_ev_dec : forall (e1 e2 : ev), {e1 = e2} + {e1 <> e2}
               }.


Record Endstates := {

              es : Type;
              an_es : es
              }.

(** A trace represents either a stopped execution, a silently diverging
    execution or an infinite execution. *)
Variant trace {E : Events} {Es : Endstates} : Type :=
| tstop (l : list (ev E)) (e : es Es) : trace
| tsilent (l : list (ev E)) : trace
| tstream (s : @stream (ev E)) : trace.


Definition finite {E: Events} {Es : Endstates} (t : @trace E Es) : Prop :=
  exists l e, t = tstop l e.

Definition infinite {E: Events} {Es : Endstates} (t : @trace E Es) : Prop :=
  ~ finite t.


(** A finite prefix is a list of evs, that can be continued (ftbd)
    or not (fstop). *)
Variant finpref {E : Events} {Es : Endstates} : Type :=
| fstop (l : list (ev E)) (es : (es Es)) : finpref
| ftbd  (l : list (ev E)) : finpref.

Tactic Notation "destruct" "finpref" ident(m) "as" ident(e) ident(f) ident(p) :=
  destruct m as [ [| e p] f
                | [| e p]
                ].

Tactic Notation "induction" "finpref" ident(m) "as" ident(e) ident(f) ident(p) ident(Hp) :=
  destruct m as [m f | m]; induction m as [|e p Hp].

(** Prefix relation between finite prefixes and traces *)
(** *prefix relation *)

Definition prefix {E : Events} {Es : Endstates}
                  (m : @finpref E Es)
                  (t : @trace E Es) : Prop :=
  match m, t with
  | fstop lm em, tstop lt et => em = et /\ lm = lt
  | ftbd  lm   , tstop lt et => list_list_prefix lm lt
  | ftbd  lm   , tsilent lt  => list_list_prefix lm lt
  | ftbd  lm   , tstream s   => list_stream_prefix lm s
  | _, _ => False
  end.

Definition prefix_finpref {E : Events} {Es : Endstates}
                          (m m' : @finpref E Es) : Prop :=
    match m, m' with
    | fstop l e, fstop l' e' => l = l' /\ e = e'
    | ftbd l, ftbd l' => l = l'
    | fstop _ _, ftbd l => False
    | ftbd l, fstop l' _ => list_list_prefix l l'
    end.


Lemma prefix_stop_terminating_trace {E : Events} {Es : Endstates}
                                    (l : @list (ev E))
                                    (e : es Es)
                                    (t : @trace E Es):
  prefix (fstop l e) t -> t = tstop l e.
Proof.
  intros H_pref. destruct t; try now inversion H_pref.
  destruct l0, l; inversion H_pref; subst; auto;
    inversion H_pref; subst.
  + inversion H1. + inversion H1. + now rewrite H0.
Qed.
