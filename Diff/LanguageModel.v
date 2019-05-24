Set Implicit Arguments.

Require Import TraceModel.
Require Import Properties.
Require Import ClassicalExtras.
Require Import MyNotation. 

Record Language := {
  
   prg : Set; (* Whole programs *)
   par : Set; (* Partial programs *)
   ctx : Set; (* Contexts *)
   plug : par -> ctx -> prg (* Linking operation *)

   }.


Section Sat.

  Variable Σ States : Set.
  Variable E : Events Σ.
  Variable S : EndState States.

  Variable L : Language.

  Local Definition trace := trace Σ States.
  Local Definition finpref := finpref Σ States.
  Local Definition prop := prop Σ States.
  Local Definition hprop := hprop Σ States. 

  Variable sem : prg L -> trace -> Prop.
  Variable non_empty_sem : forall W, exists t, sem W t.  
  
  Definition beh (P : prg L) : prop :=
    fun b => sem P b.

  Definition sat (P : prg L) (π : prop) : Prop :=
    forall t, sem P t -> π t.

  Lemma sat_upper_closed  (P : prg L ) (π1 π2 : prop) :
                          sat P π1 -> π1 ⊆ π2 -> sat P π2.  
  Proof.  
    intros Hsat1 Hsuper t Hsem.
    apply Hsuper.
    now apply (Hsat1 t).  
  Qed. 

  
  Definition hsat (P : prg L) (H : hprop) : Prop :=
    H (beh P).

  Definition rsat (P : par L) (π : prop) : Prop :=
    forall C, sat (plug L P C) π.
  
  Lemma rsat_upper_closed  (P : par L ) (π1 π2 : prop) :
                            rsat P π1 -> π1 ⊆ π2 -> rsat P π2.  
  Proof.  
    intros Hsat1 Hsuper C t Hsem.
    apply Hsuper.
    now apply (Hsat1 C t).  
  Qed. 

  Definition rhsat (P : par L) (H : hprop) : Prop :=
    forall C, hsat (plug L P C) H.

  Lemma neg_sat :
    forall (W : prg L) (π : prop),
      ~ sat W π <-> exists t, sem W t /\ ~ π t.
  Proof.
    intros W π. unfold sat.
    rewrite not_forall_ex_not.
    split; intros [t H]; exists t; [now rewrite not_imp in H
                               | now rewrite not_imp].                            
  Qed. 

  (* Considering moving these two lemmas to a separate module *)
  Lemma neg_rsat :
    forall (P : par L) (π : prop),
      (~ rsat P π <->
       (exists C t, sem (plug L P C) t /\ ~ π t)).
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
  
  Lemma neg_rhsat :
    forall P H,  (~ rhsat P H <-> ( exists (C : ctx L), ~ H (beh ( plug L P C )))).
  Proof.
    intros P H.
    split; unfold rhsat; intro H0;
      [now rewrite <- not_forall_ex_not | now rewrite not_forall_ex_not].
  Qed.
  
End Sat.


