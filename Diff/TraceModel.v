From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.
Require Import Stream.

Record Events (event : Set) := {

                  an_event : event;
                  another_event : event;
                  different_events : an_event <> another_event;
                  eq_event_dec : forall (e1 e2 : event), {e1 = e2} + {e1 <> e2} 

                }. 

Record EndState (endstate : Set) := { an_endstate : endstate }. 

Section Trace.

  Variable event : Set.
  Variable endstate : Set.

  Variable events : Events event. 
  Variable endstates : EndState endstate.
  
  (** A trace represents either a stopped execution, a silently diverging
    execution or an infinite execution. *)
  Variant trace : Set :=
  | tstop (l : list event) (e : endstate) : trace
  | tsilent (l : list event) : trace
  | tstream (s : @stream event) : trace.
  

  Definition finite (t : trace): Prop :=
    exists l e, t = tstop l e.

  Definition infinite (t : trace): Prop := ~ finite t. 
  

  (** A finite prefix is a list of events, that can be continued (ftbd)
    or not (fstop). *)
  Variant finpref : Set :=
  | fstop (l : list event) (es : endstate) : finpref
  | ftbd  (l : list event) : finpref. 

  Tactic Notation "destruct" "finpref" ident(m) "as" ident(e) ident(f) ident(p) :=
    destruct m as [ [| e p] f
                  | [| e p]
                  ].

  Tactic Notation "induction" "finpref" ident(m) "as" ident(e) ident(f) ident(p) ident(Hp) :=
    destruct m as [m f | m]; induction m as [|e p Hp].

  (** Prefix relation between finite prefixes and traces *)
  (** *prefix relation *)

  Definition prefix (m : finpref) (t : trace) : Prop :=
    match m, t with
    | fstop lm em, tstop lt et => em = et /\ lm = lt
    | ftbd  lm   , tstop lt et => list_list_prefix lm lt
    | ftbd  lm   , tsilent lt  => list_list_prefix lm lt
    | ftbd  lm   , tstream s   => list_stream_prefix lm s
    | _, _ => False
    end.

  Definition prefix_finpref (m m' : finpref) : Prop :=
    match m, m' with
    | fstop l e, fstop l' e' => l = l' /\ e = e'
    | ftbd l, ftbd l' => l = l'
    | fstop _ _, ftbd l => False
    | ftbd l, fstop l' _ => list_list_prefix l l'
    end.

End Trace.


