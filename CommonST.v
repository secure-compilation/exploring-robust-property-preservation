Require Import TraceModel.
Require Import Properties.
Require Import ClassicalExtras.
Require Import Events.

(** This file defines the notion of language and of compilation
    chain we use in the rest of the development *)

Set Implicit Arguments.

Record language :=
  {
    par  : Set;  (* partial programs *)
    prg  : Set;  (* whole programs *)
    ctx  : Set;  (* context *)
    plug : par -> ctx -> prg;
    sem  : prg -> prop;
    non_empty_sem : forall W, exists t, sem W t
  }.


Axiom src : language.
Axiom tgt : language.
Axiom compile_par : (par src) -> (par tgt).
Axiom compile_ctx : (ctx src) -> (ctx tgt).
Axiom compile_prg : (prg src) -> (ctx tgt).

Notation "C [ P ]" := (plug _ P C) (at level 50).
Notation "P ↓" := (compile_par P) (at level 50).


Definition psem {K : language}
                (P : prg K)
                (m : finpref) : Prop :=
  exists t, prefix m t /\ (sem K) P t.

Definition sat {K : language}
               (P : prg K)
               (π : prop) : Prop :=
  forall t, sem K P t -> π t.

Definition rsat {K : language}
                (P : par K)
                (π : prop) : Prop :=
  forall C, sat (C [ P ] ) π.


Lemma neg_rsat {K : language} :
    forall P π, (~ rsat P π <->
           (exists C t, sem K (C [ P ]) t /\ ~ π t)).
Proof.
   unfold rsat. unfold sat. split.
  - intros r. rewrite not_forall_ex_not in r.
    destruct r as [C r]. rewrite not_forall_ex_not in r.
    destruct r as [t r]. exists C,t. rewrite not_imp in r.
    assumption.
  - intros [C [t r]]. rewrite not_forall_ex_not.
    exists C. rewrite not_forall_ex_not. exists t.
    rewrite not_imp. assumption.
Qed.


Definition beh {K : language} (P : prg K) : prop :=
  fun b => sem K P b.

Definition hsat {K : language}
                (P : prg K)
                (H : hprop) : Prop :=
  H (beh P).

Definition rhsat {K : language}
                 (P : par K)
                 (H : hprop) : Prop :=
  forall C, hsat ( C [ P ] ) H.

Lemma neg_rhsat {K : language} :
  forall P H,  (~ rhsat P H <-> ( exists (C : ctx K), ~ H (beh ( C [ P ] )))).
Proof.
  intros P H. split; unfold rhsat; intro H0;
  [now rewrite <- not_forall_ex_not | now rewrite not_forall_ex_not].
Qed.

Definition sat2 {K : language} (P1 P2 : @prg K) (r : rel_prop) : Prop :=
  forall t1 t2, sem K P1 t1 -> sem K P2 t2 -> r t1 t2.

Lemma neg_sat2 {K : language} : forall P1 P2 r,
    ~ sat2 P1 P2 r <-> (exists t1 t2, sem K P1 t1 /\ sem K P2 t2 /\ ~ r t1 t2).
Proof.
  unfold sat2. intros P1 P2 r. split.
  +  intros H. rewrite not_forall_ex_not in H.
    destruct H as [t1 H]. rewrite not_forall_ex_not in H.
    destruct H as [t2 H]. rewrite not_imp in H. destruct H as [H1 H2].
    rewrite not_imp in H2. destruct H2 as [H2 H3].
    now exists t1, t2.
  + intros [t1 [t2  [H1 [H2 H3]]]]. rewrite not_forall_ex_not.
    exists t1. rewrite not_forall_ex_not. exists t2.
    rewrite not_imp. split.
    ++ assumption.
    ++ rewrite not_imp. now auto.
Qed.


Definition rsat2 {K : language} (P1 P2 : @par K) (r : rel_prop) : Prop :=
  forall C, sat2 (C [ P1 ]) (C [ P2 ]) r.


Definition hsat2 {K : language} (P1 P2 : @prg K) (r : rel_hprop) : Prop :=
   r (sem K P1) (sem K P2).

Definition hrsat2 {K : language} (P1 P2 : @par K) (r : rel_hprop) : Prop :=
  forall C, r (sem K (C [P1])) (sem K (C [P2])).

(**************************************************************************)

Definition input_totality (K : language) : Prop :=
  forall (P : prg K) m e1 e2,
    is_input e1  -> is_input e2 -> fstopped m = false ->
    psem P (fsnoc m e1) -> psem P (fsnoc m e2).

Definition traces_match (t1 t2 : trace) : Prop :=
 t1 = t2 \/
 (exists (m : finpref) (e1 e2 : event),
   is_input e1 /\ is_input e2 /\  e1 <> e2 /\
   fstopped m = false /\ prefix (fsnoc m e1) t1 /\ prefix (fsnoc m e2) t2).

Definition determinacy (K : language) : Prop :=
  forall (P : prg K) t1 t2,
    sem K P t1 -> sem K P t2 -> traces_match t1 t2.

Definition semantics_safety_like (K : language) : Prop :=
  forall t P,
    ~ sem K P t -> inf t -> ~ diverges t ->
    (exists m ebad, psem P m /\ prefix (fsnoc m ebad) t /\ ~ psem P (fsnoc m ebad)).
