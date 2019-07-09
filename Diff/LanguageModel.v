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

Record Semantics (L : Language) (trace_set : Type) := {

  sem : prg L -> trace_set -> Prop;
  non_empty_sem : forall W, exists t, sem W t

  }.


Definition beh {L : Language}
               {trace_set : Type}
               (S : Semantics L trace_set)
               (W : prg L) : prop trace_set :=
  fun t => sem S W t.

Definition sat {L : Language}
               {trace_set : Type}
               (S : Semantics L trace_set)
               (W : prg L) (π : prop trace_set) : Prop :=
  forall t, sem S W t -> π t.

Lemma sat_upper_closed  {L : Language}
                        {trace_set : Type}
                        (S : Semantics L trace_set)
                        (W : prg L ) (π1 π2 : prop trace_set) :
  sat S W π1 -> π1 ⊆ π2 -> sat S W π2.
Proof.
  intros Hsat1 Hsuper t Hsem.
  apply Hsuper.
  now apply (Hsat1 t).
Qed.


Definition hsat{L : Language}
               {trace_set : Type}
               (S : Semantics L trace_set)
               (W : prg L) (H : hprop trace_set) : Prop :=
  H (beh S W).

Lemma hsat_upper_closed  {L : Language}
                         {trace_set : Type}
                         (S : Semantics L trace_set)
                         (W : prg L ) (H1 H2 : hprop trace_set) :
  hsat S W H1 -> H1 ⊆ H2 -> hsat S W H2.
Proof.
  intros Hsat1 Hsuper.
  apply Hsuper.
  now apply Hsat1. 
Qed.


Definition rsat {L : Language}
                {trace_set : Type}
                (S : Semantics L trace_set)
                (P : par L) (π : prop trace_set) : Prop :=
  forall C, sat S (plug L P C) π.

Lemma rsat_upper_closed {L : Language}
                        {trace_set : Type}
                        (S : Semantics L trace_set)
                        (P : par L ) (π1 π2 : prop trace_set) :
  rsat S P π1 -> π1 ⊆ π2 -> rsat S P π2.
Proof.
  intros Hsat1 Hsuper C t Hsem.
  apply Hsuper.
  now apply (Hsat1 C t).
Qed.

Definition rhsat  {L : Language}
                  {trace_set : Type}
                  (S : Semantics L trace_set)
                  (P : par L) (H : hprop trace_set) : Prop :=
  forall C, hsat S (plug L P C) H.

Lemma neg_sat  {L : Language}
               {trace_set : Type}
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
               {trace_set : Type}
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
                {trace_set : Type}
                (S : Semantics L trace_set) :
  forall P H,  (~ rhsat S P H <-> ( exists (C : ctx L), ~ H (beh S ( plug L P C )))).
Proof.
  intros P H.
  split; unfold rhsat; intro H0;
    [now rewrite <- not_forall_ex_not | now rewrite not_forall_ex_not].
Qed.


Lemma rhsat_upper_closed {L : Language}
                         {trace_set : Type}
                         (S : Semantics L trace_set)
                         (P : par L ) (H1 H2 : hprop trace_set) :
  rhsat S P H1 -> H1 ⊆ H2 -> rhsat S P H2.  
Proof.
  intros rsat1 Hsuper C. 
  apply Hsuper.
  now apply (rsat1 C).
Qed. 


Definition sat2 {L : Language}
                {trace_set : Type}
                (S : Semantics L trace_set)
                (W1 W2 : prg L) (R : trace_set * trace_set -> Prop) : Prop :=
  forall t1 t2, sem S W1 t1 -> sem S W2 t2 -> R (t1, t2).

Definition rsat2 {L : Language}
                 {trace_set : Type}
                 (S : Semantics L trace_set)
                 (P1 P2 : par L) (R : trace_set * trace_set -> Prop) : Prop :=
  forall C t1 t2, sem S (plug L P1 C) t1 -> sem S (plug L P2 C) t2 -> R (t1, t2).

Lemma sat2_upper_closed  {L : Language}
                         {trace_set : Type}
                         (S : Semantics L trace_set)
                         (W1 W2 : prg L ) (R1 R2 : trace_set * trace_set -> Prop) :
  sat2 S W1 W2 R1 -> R1 ⊆ R2 -> sat2 S W1 W2 R2.
Proof.
  intros Hsat1 Hsuper t1 t2 Hsem1 Hsem2.
  apply Hsuper.
  now apply (Hsat1 t1).
Qed.

Lemma rsat2_upper_closed {L : Language}
                         {trace_set : Type}
                         (S : Semantics L trace_set)
                         (P1 P2 : par L ) (R1 R2 : trace_set * trace_set -> Prop) :
  rsat2 S P1 P2 R1 -> R1 ⊆ R2 -> rsat2 S P1 P2 R2.
Proof.
  intros Hsat1 Hsuper C t1 t2 Hsem1 Hsem2.
  apply Hsuper.
  now apply (Hsat1 C t1).
Qed.

Lemma neg_sat2  {L : Language}
                {trace_set : Type}
                {S : Semantics L trace_set} :
  forall (W1 W2 : prg L) (R : trace_set * trace_set -> Prop),
    ~ sat2 S W1 W2 R <-> exists t1 t2, sem S W1 t1 /\ sem S W2 t2 /\ ~ R (t1, t2).
Proof.
  intros W1 W2 R. unfold sat2.
  rewrite not_forall_ex_not.
  split.
  + intros [t1 H]. rewrite not_forall_ex_not in H.
    destruct H as [t2 H]. rewrite not_imp in H. destruct H as [H1 H].
    rewrite not_imp in H. destruct H as [H2 H]. 
    now exists t1, t2.
  + intros [t1 [t2 [H1 [H2 H]]]].
    exists t1. rewrite not_forall_ex_not. exists t2. firstorder.
Qed.

Lemma neg_rsat2 {L : Language}
                {trace_set : Type}
                (S : Semantics L trace_set) :
  forall (P1 P2 : par L) (R: trace_set * trace_set -> Prop),
    (~ rsat2 S P1 P2 R <->
     (exists C t1 t2, sem S (plug L P1 C) t1 /\ sem S (plug L P2 C) t2 /\ ~ R (t1,t2))).
Proof.
  intros P1 P2 R.
  split; unfold rsat2; intros H.
  - rewrite not_forall_ex_not in H.
    destruct H as [C H]; exists C.
    unfold sat2 in H; rewrite not_forall_ex_not in H.
    destruct H as [t1 H]; exists t1.
    rewrite not_forall_ex_not in H.
    destruct H as [t2 H]; exists t2. 
    now rewrite !not_imp in H.
  - firstorder.
Qed.

Definition hsat2 {L : Language}
                 {trace_set : Type}
                 (S : Semantics L trace_set)
                 (W1 W2 : prg L) (R : (prop trace_set) * (prop trace_set) -> Prop) : Prop :=
  R ((beh S W1), (beh S W2)).

Definition rhsat2 {L : Language}
                  {trace_set : Type}
                  (S : Semantics L trace_set)
                  (P1 P2 : par L) (R : (prop trace_set) * (prop trace_set) -> Prop) : Prop :=
  forall C, hsat2 S (plug L P1 C) (plug L P2 C) R.


Lemma neg_rhsat2 {L : Language}
                 {trace_set : Type}
                 (S : Semantics L trace_set) :
  forall P1 P2 R,  (~ rhsat2 S P1 P2 R <-> ( exists (C : ctx L),
                                        ~ R ((beh S (plug L P1 C )),(beh S (plug L P2 C))))).
Proof.
  intros P1 P2 R.
  split; unfold rhsat2; intro H0;
    [now rewrite <- not_forall_ex_not | now rewrite not_forall_ex_not].
Qed.


Lemma rhsat2_upper_closed {L : Language}
                          {trace_set : Type}
                          (S : Semantics L trace_set)
                          (P1 P2 : par L ) (R1 R2 : (prop trace_set) * (prop trace_set) -> Prop) :
  rhsat2 S P1 P2 R1 -> R1 ⊆ R2 -> rhsat2 S P1 P2 R2.  
Proof.
  intros rsat_one Hsuper C. 
  apply Hsuper.
  now apply (rsat_one C).
Qed. 
