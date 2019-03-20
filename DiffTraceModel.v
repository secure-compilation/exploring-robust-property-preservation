From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import DiffEvents.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List. 

CoInductive stream {A : Type} :=
   scons (e : A) (s : stream) : stream. 

Fixpoint list_stream_prefix {A : Type} (l : list A) (s : stream) :=
  match l, s with
  | nil, _ => True
  | cons a1 l1, scons a2 s2 => (a1 = a2) /\ (list_stream_prefix l1 s2)
  end.  

Fixpoint list_list_prefix {A : Type} (l1 l2 : list A) :=
  match l1, l2 with
  | nil, _ => True
  | cons a1 l1, cons a2 l2 => (a1 = a2) /\ list_list_prefix l1 l2
  | _, _ => False
  end.

Lemma list_list_prefix_ref {A : Type} (l : list A) : list_list_prefix l l. 
Proof. now induction l. Qed. 

Lemma list_list_prefix_asym {A : Type} : forall (l1 l2 : list A),
    list_list_prefix l1 l2 -> list_list_prefix l2 l1 -> l1 = l2. 
Proof.
  induction l1, l2; try now auto.
  simpl. intros [afoo Hpref] [afoo' Hpref']; subst; now rewrite (IHl1 l2). 
Qed.

Lemma list_list_prefix_trans {A : Type} : forall l1 l2 l3 : list A,
  list_list_prefix l1 l2 -> list_list_prefix l2 l3 -> list_list_prefix l1 l3.
Proof.
  induction l1; try now auto.  
  intros [] [] H1 H2; inversion H1; inversion H2; subst.
  simpl. firstorder.
Qed.

Lemma list_stream_prefix_trans {A : Type} : forall (l1 l2 : list A) (s : stream),
    list_list_prefix l1 l2 -> list_stream_prefix l2 s ->
    list_stream_prefix l1 s.
Proof.
  induction l1; auto.
  + intros [] [] Hpref1 Hpref2; inversion Hpref1; inversion Hpref2; subst. 
    simpl. split; auto; now apply (IHl1 l s).
Qed.

(** A trace represents either a stopped execution, a silently diverging
    execution or an infinite execution. *)
Variant trace {k : level} : Set :=
| tstop (l : list (event k)) (e : (endstate k)) : trace
| tsilent (l : list (event k)) : trace
| tstream (s : @stream (event k)) : trace.


(** A finite prefix is a list of events, that can be continued (ftbd)
    or not (fstop). *)
Variant finpref {k : level} : Set :=
| fstop (l : list (event k)) (es : (endstate k)) : finpref
| ftbd  (l : list (event k)) : finpref. 

Tactic Notation "destruct" "finpref" ident(m) "as" ident(e) ident(f) ident(p) :=
  destruct m as [ [| e p] f
                | [| e p]
                ].

Tactic Notation "induction" "finpref" ident(m) "as" ident(e) ident(f) ident(p) ident(Hp) :=
  destruct m as [m f | m]; induction m as [|e p Hp].

(** Prefix relation between finite prefixes and traces *)
(** *prefix relation *)

Definition prefix {k : level} (m : @finpref k) (t : @trace k) : Prop :=
  match m, t with
  | fstop lm em, tstop lt et => em = et /\ lm = lt
  | ftbd  lm   , tstop lt et => list_list_prefix lm lt
  | ftbd  lm   , tsilent lt  => list_list_prefix lm lt
  | ftbd  lm   , tstream s   => list_stream_prefix lm s
  | _, _ => False
  end.


Definition prop {k : level} := @trace k -> Prop. 