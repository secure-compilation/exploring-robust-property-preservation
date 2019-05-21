Require Import TraceModel.
Require Import Properties.
Require Import ClassicalExtras.
Require Import MyNotation. 

Module Type Language.

  Parameter prg : Set. (* Whole programs *)
  Parameter par : Set. (* Partial programs *)
  Parameter ctx : Set. (* Contexts *)
  Parameter plug : par -> ctx -> prg. (* Linking operation *)

End Language.

Module Sat (T : Trace) (L : Language).

  Module P := Properties T.

  Import T L P.
  
  Parameter sem : prg -> trace -> Prop.

  Parameter non_empty_sem : forall W, exists t, sem W t.
  
  Definition beh (P : prg) : prop :=
    fun b => sem P b.

  Definition sat (P : prg) (π : prop) : Prop :=
    forall t, sem P t -> π t.

  Lemma sat_upper_closed  (P : L.prg ) (π1 π2 : P.prop) :
                          sat P π1 -> π1 ⊆ π2 -> sat P π2.  
  Proof.  
    intros Hsat1 Hsuper t Hsem.
    apply Hsuper.
    now apply (Hsat1 t).  
  Qed. 

  
  Definition hsat (P : prg) (H : hprop) : Prop :=
    H (beh P).

  Definition rsat (P : par) (π : prop) : Prop :=
    forall C, sat (plug P C) π.
  
  Lemma rsat_upper_closed  (P : L.par ) (π1 π2 : P.prop) :
                            rsat P π1 -> π1 ⊆ π2 -> rsat P π2.  
  Proof.  
    intros Hsat1 Hsuper C t Hsem.
    apply Hsuper.
    now apply (Hsat1 C t).  
  Qed. 

  Definition rhsat (P : par) (H : hprop) : Prop :=
    forall C, hsat (plug P C) H.

  (* Considering moving these two lemmas to a separate module *)
  Lemma neg_rsat :
    forall (P : par) (π : prop),
      (~ rsat P π <->
       (exists C t, sem (plug P C) t /\ ~ π t)).
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
    forall P H,  (~ rhsat P H <-> ( exists (C : ctx), ~ H (beh ( plug P C )))).
  Proof.
    intros P H.
    split; unfold rhsat; intro H0;
      [now rewrite <- not_forall_ex_not | now rewrite not_forall_ex_not].
  Qed.
  
End Sat.
