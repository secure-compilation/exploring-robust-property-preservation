From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Require Import DiffEvents.
Require Import DiffTraceModel.
Require Import DiffProperties.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.

Record language {k : level} :=
  {
    par  : Set;  (* partial programs *)
    prg  : Set;  (* whole programs *)
    ctx  : Set;  (* context *)
    plug : par -> ctx -> prg;
    sem  : prg -> @prop k;
    non_empty_sem : forall W, exists t, sem W t
  }.


Axiom src : @language source.
Axiom tgt : @language target.
Axiom compile_par : (par src) -> (par tgt).
Axiom compile_ctx : (ctx src) -> (ctx tgt).
Axiom compile_prg : (prg src) -> (ctx tgt).

(*TODO: fix notation *)
Notation "C [ P ]" := (plug P C) (at level 50).

Notation "P ↓" := (compile_par P) (at level 50).

Definition sat {k : level}
               {K : language}
               (P : prg K)
               (π : @prop k) : Prop :=
  forall t, sem P t -> π t.

Definition rsat {k : level}
                {K : @language k}
                (P : par K)
                (π : @prop k) : Prop :=
  forall C, sat (plug P C) π.

Lemma neg_rsat {k : level} {K : @language k} :
  forall (P : @par k K) (π : @prop k),
    (~ rsat P π <->
           (exists C t, sem (plug P C) t /\ ~ π t)).
Proof.  
Admitted. (* TODO: port this proof in ssreflect style *)

Definition beh {k : level} {K : language} (P : prg K) : prop :=
  fun b => @sem k K P b.

Definition hsat {k : level}
                {K : @language k}
                (P : prg K)
                (H : @hprop k) : Prop :=
  H (beh P).

Definition rhsat {k : level}
                 {K : @language k}
                 (P : par K)
                 (H : hprop) : Prop :=
  forall C, hsat ( plug P C ) H.

Lemma neg_rhsat {k : level} {K : @language k} :
  forall P H,  (~ rhsat P H <-> ( exists (C : ctx K), ~ H (beh ( plug P C )))).
Proof.
  intros P H. split; unfold rhsat; intro H0;
  [now rewrite <- not_forall_ex_not | now rewrite not_forall_ex_not].
Qed.

