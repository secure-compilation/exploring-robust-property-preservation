From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.
Require Import Stream.


Module Type Trace.
  Parameter event : Set.  
  Parameter an_event another_event : event.
  Parameter different_events : an_event <> another_event.
  Parameter eq_event_dec : forall (e1 e2 : event), {e1 = e2} + {e1 <> e2}. 

  Parameter endstate : Set.
  Parameter an_endstate : endstate.

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

End Trace.