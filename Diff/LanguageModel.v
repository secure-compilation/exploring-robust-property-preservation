Set Implicit Arguments.

Require Import TraceModel.
Require Import Properties.
Require Import ClassicalExtras.
Require Import MyNotation.

Record Language := {

   prg : Type; (* Whole programs *)
   par : Type; (* Partial programs *)
   ctx : Type; (* Contexts *)
   plug : par -> ctx -> prg (* Linking operation *)

   }.


(* CA: semantics of a language can be defined over an arbitrary set *)

Record Semantics (L : Language) (trace_set : Set) := {

  sem : prg L -> trace_set -> Prop;
  non_empty_sem : forall W, exists t, sem W t

  }.


Definition beh {L : Language}
               {trace_set : Set}
               (S : Semantics L trace_set)
               (W : prg L) : prop trace_set :=
  fun t => sem S W t.

Definition sat {L : Language}
               {trace_set : Set}
               (S : Semantics L trace_set)
               (W : prg L) (π : prop trace_set) : Prop :=
  forall t, sem S W t -> π t.

Lemma sat_upper_closed  {L : Language}
                        {trace_set : Set}
                        (S : Semantics L trace_set)
                        (W : prg L ) (π1 π2 : prop trace_set) :
  sat S W π1 -> π1 ⊆ π2 -> sat S W π2.
Proof.
  intros Hsat1 Hsuper t Hsem.
  apply Hsuper.
  now apply (Hsat1 t).
Qed.


Definition hsat{L : Language}
               {trace_set : Set}
               (S : Semantics L trace_set)
               (W : prg L) (H : hprop trace_set) : Prop :=
  H (beh S W).

Definition rsat {L : Language}
                {trace_set : Set}
                (S : Semantics L trace_set)
                (P : par L) (π : prop trace_set) : Prop :=
  forall C, sat S (plug L P C) π.

Lemma rsat_upper_closed {L : Language}
                        {trace_set : Set}
                        (S : Semantics L trace_set)
                        (P : par L ) (π1 π2 : prop trace_set) :
  rsat S P π1 -> π1 ⊆ π2 -> rsat S P π2.
Proof.
  intros Hsat1 Hsuper C t Hsem.
  apply Hsuper.
  now apply (Hsat1 C t).
Qed.

Definition rhsat  {L : Language}
                  {trace_set : Set}
                  (S : Semantics L trace_set)
                  (P : par L) (H : hprop trace_set) : Prop :=
  forall C, hsat S (plug L P C) H.

Lemma neg_sat  {L : Language}
               {trace_set : Set}
               {S : Semantics L trace_set} :
  forall (W : prg L) (π : prop trace_set),
    ~ sat S W π <-> exists t, sem S W t /\ ~ π t.
Proof.
  intros W π. unfold sat.
  rewrite not_forall_ex_not.
  split; intros [t H]; exists t; [now rewrite not_imp in H
                            | now rewrite not_imp].
Qed.

(* Considering moving these two lemmas to a separate module *)
Lemma neg_rsat {L : Language}
               {trace_set : Set}
               (S : Semantics L trace_set) :
  forall (P : par L) (π : prop trace_set),
    (~ rsat S P π <->
     (exists C t, sem S (plug L P C) t /\ ~ π t)).
Proof.
  intros P π.
  split; unfold rsat; intros H.
  - rewrite not_forall_ex_not in H.
    destruct H as [C H]; exists C.
    unfold sat in H; rewrite not_forall_ex_not in H.
    destruct H as [t H]; exists t.
    now rewrite not_imp in H.
  - firstorder.
Qed.

Lemma neg_rhsat {L : Language}
                {trace_set : Set}
                (S : Semantics L trace_set) :
  forall P H,  (~ rhsat S P H <-> ( exists (C : ctx L), ~ H (beh S ( plug L P C )))).
Proof.
  intros P H.
  split; unfold rhsat; intro H0;
    [now rewrite <- not_forall_ex_not | now rewrite not_forall_ex_not].
Qed.


Lemma rhsat_upper_closed {L : Language}
                         {trace_set : Set}
                         (S : Semantics L trace_set)
                         (P : par L ) (H1 H2 : hprop trace_set) :
  rhsat S P H1 -> H1 ⊆ H2 -> rhsat S P H2.  
Proof.
  intros rsat1 Hsuper C. 
  apply Hsuper.
  now apply (rsat1 C).
Qed. 
