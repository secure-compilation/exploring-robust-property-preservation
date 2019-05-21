From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Require Import FunctionalExtensionality.
Require Import ClassicalExtras.
Require Import MyNotation.

Require Import TraceModel.

Module Properties (T : Trace).
  Import T.
  
  Definition prop := trace -> Prop.
  Definition fprop := finpref -> Prop.
  
  Notation "M <<< b" := (forall m, M m -> exists t, b t /\ prefix m t) (at level 50).  

  Definition Safety (π : prop) : Prop :=
    forall t, ~ π t ->
         (exists m, prefix m t /\
               (forall t', prefix m t' -> ~ π t')).

  Inductive Observations : (finpref -> Prop) -> Prop :=
    empty :  Observations (fun m : finpref => False)
  | finite_union : forall M m, Observations M -> Observations (fun x => M x \/ x = m).

  
  (* CA: for now this is axiomatized but we can recover it by modifying
       results from TraceTopology.v *)
  Definition Cl (π : prop) : prop :=
    fun t => forall S, Safety S -> π ⊆ S -> S t.   
  
  Lemma Cl_bigger (π: prop) : π ⊆ (Cl π). 
  Proof. firstorder. Qed. 

  Lemma Cl_Safety (π: prop): Safety (Cl π).
  Proof.
    move => t not_π_t.
    move/not_forall_ex_not: not_π_t. move => [π' H].
    move/not_imp: H. move => [safety_π' H].
    move/not_imp: H. move => [π_leq_π' not_π'_t].
    destruct (safety_π' t not_π'_t) as [m [m_leq_t m_wit]].
    exists m. split; auto. move => t' m_leq_t' Hf.
    apply: (m_wit t'). assumption. by apply: Hf. 
  Qed.

  Hypothesis prop_extensionality : forall A B:Prop, (A <-> B) -> A = B. 

  Lemma Cl_id_on_Safe (π: prop): Safety π -> Cl π = π.
  Proof.
    move => Safety_π. apply: functional_extensionality => t.
    apply: prop_extensionality.
      by firstorder. 
  Qed.  
  
  Lemma Cl_smallest (π :prop) : forall S, Safety S -> π ⊆ S -> Cl π ⊆ S.
  Proof. by firstorder. Qed. 

  Definition hprop := prop -> Prop.

  Definition SSC  (H: hprop)  : Prop :=
    forall h, H h ->
         (forall b : prop, b ⊆ h -> H b).

  Definition sCl (H : hprop) : hprop :=
    fun b => exists b', H b' /\ b ⊆ b'.

  Lemma sCl_bigger (H : hprop) : H ⊆ (sCl H). 
  Proof. firstorder. Qed.   
  
  Lemma sCl_SCH (H : hprop) : SSC (sCl H).
  Proof.
    move => h [b' [Hb' bb']] b b_h. exists b'; auto.
  Qed.

  Lemma sCl_id_on_SSC (H: hprop): SSC H -> sCl H = H.
  Proof.
    move => H_SSC. apply: functional_extensionality => b.
    apply: prop_extensionality. firstorder. 
  Qed.

  Lemma sCl_smallest (H: hprop):
    forall H', SSC H' -> H ⊆ H' -> (sCl H) ⊆ H'.
  Proof.
    move => H' ssc_H' H_leq_H' b [b' [ b_leq_b' H_b']].
    apply: (ssc_H' b'); auto.
  Qed.   
  
  Definition HSafe (H: hprop) :=
    forall b, ~ H b -> (exists M, Observations M /\ M <<< b /\
                       (forall b', M <<< b' -> ~ H b')). 

  Definition hsCl (H: hprop): hprop :=
    fun b => forall Hs, HSafe Hs -> H ⊆ Hs -> Hs b. 
  
  Lemma hsCl_bigger (H: hprop): H ⊆ hsCl H.
  Proof. by firstorder. Qed. 

  Lemma hsCl_HSafe (H: hprop): HSafe (hsCl H). 
  Proof.
    move => b. move/not_forall_ex_not => not_H_b. 
    destruct not_H_b as [H' not_H'_b].
    move/not_imp: not_H'_b. move => [HSafe_H' not_H'_b].
    move/not_imp: not_H'_b. move => [H_leq_H' not_H'_b].
    destruct (HSafe_H' b not_H'_b) as [M [obs_M [M_leq_b M_wit]]].
    exists M. repeat (split; auto).
    move => b' M_leq_b' Hf. apply: (M_wit b'); auto. 
      by apply: Hf.
  Qed.     
  
  Lemma HSafe_SCH  : forall (H: hprop), HSafe H -> SSC H.
  Proof. 
    move => H HSafe_H b Hb b' b'_leq_b. 
    apply: NNPP => not_H_b'.
    destruct (HSafe_H b' not_H_b') as [M [obs_M [M_leq_b' M_wit]]].
    apply: (M_wit b); firstorder. 
  Qed. 
  
  Lemma sCl_id_on_HSafe : forall (H: hprop), HSafe H -> sCl H = H.
  Proof.
    move => H HSafe_H.
    have SSC_H: (SSC H) by apply: HSafe_SCH.
      by rewrite (sCl_id_on_SSC SSC_H). 
  Qed.   
  
  Lemma hsCl_sCl : forall (H: hprop), sCl H ⊆ hsCl H.  
  Proof.
    move => H.
    have ssc: SSC (hsCl H).
    { apply: HSafe_SCH. apply: hsCl_HSafe. }
    apply: sCl_smallest; auto.
      by apply: hsCl_bigger.
  Qed.

  Lemma hsCl_smallest (H: hprop):
    forall H', HSafe H' -> H ⊆ H' -> (hsCl H) ⊆ H'.
  Proof. by firstorder. Qed.


  Definition Dense (π: prop): Prop :=
    forall t, finite t -> π t.

  Definition dCl : prop -> prop :=
    fun π => (fun t => finite t \/ π t).

  Lemma Dense_dCl (π: prop): Dense (dCl π).
  Proof. firstorder. Qed.

End Properties.