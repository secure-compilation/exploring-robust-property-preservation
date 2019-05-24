From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Require Import FunctionalExtensionality.
Require Import ClassicalExtras.
Require Import MyNotation.

Require Import TraceModel.
Require Import Galois. 

Section Properties.

  Variable Σ States : Set.
  Variable E : Events Σ.
  Variable S : EndState States.

  Local Definition trace := trace Σ States.
  Local Definition finpref := finpref Σ States.

  Hypothesis prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.
  
  Definition prop  := trace -> Prop. 
  Definition fprop := finpref -> Prop.
  Definition hprop := prop -> Prop.

  Definition h_true : hprop := fun b => True.
  
  Notation "M <<< b" := (forall m, M m -> exists t, b t /\ prefix m t) (at level 50).  

  Definition Safety (π : prop) : Prop :=
    forall t, ~ π t ->
         (exists m, prefix m t /\
               (forall t', prefix m t' -> ~ π t')).

  (* Alternate characterization of safety *)
  Definition Safety' (π : prop) : Prop:=
    exists π': fprop,
    forall t:trace, ~(π t) <-> (exists m, prefix m t /\ π' m).

  Lemma safety_safety' : forall π, Safety π <-> Safety' π.
  Proof.
    unfold Safety, Safety'. intro π. split; intro H.
    - exists (fun m => forall t, prefix m t -> ~π t).
      intros t. split; intro H'.
      + specialize (H t H'). destruct H as [m [H1 H2]].
        exists m. split. assumption. intros t' H. apply H2. assumption.
      + destruct H' as [m [H1 H2]]. apply H2. assumption.
    - intros t H0. destruct H as [π' H].
      apply H in H0. destruct H0 as [m [H1 H2]].
      exists m. split; try now auto.
      intros. rewrite H. now exists m.
  Qed.

  Inductive Observations : (finpref -> Prop) -> Prop :=
    empty :  Observations (fun m : finpref => False)
  | finite_union : forall M m, Observations M -> Observations (fun x => M x \/ x = m).

  (*****************************************************************************)
  (** *Safety closure operator                                                 *)
  (*****************************************************************************)
  
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
 
  Lemma Cl_id_on_Safe (π: prop): Safety π -> Cl π = π.
  Proof.
    move => Safety_π. apply: functional_extensionality => t.
    apply: prop_extensionality.
      by firstorder. 
  Qed.  
  
  Lemma Cl_smallest (π :prop) : forall S, Safety S -> π ⊆ S -> Cl π ⊆ S.
  Proof. by firstorder. Qed.

  Lemma Cl_mono : monotone Cl.
  Proof. 
    move => π1 π2 sub t cl2_t.
    apply: cl2_t.
    apply: Cl_Safety. apply: subset_trans. exact: sub. exact: Cl_bigger.
  Qed.  

  Lemma Cl_idmp : idempotent Cl. 
  Proof. move => π. apply: Cl_id_on_Safe. apply: Cl_Safety. Qed.
 
  
  Definition safety_uco := Build_Uco Cl_mono
                                     Cl_idmp
                                     Cl_bigger.
  

  Lemma Safety_Cl_prop :
    Safety = (lift (uco safety_uco)) h_true.  
  Proof.
    apply: functional_extensionality => π.  
    apply: prop_extensionality. split => H. 
    + exists π. split; rewrite //=.
        by rewrite Cl_id_on_Safe. 
    + move: H. rewrite //=. move => [b [H Heq]]. subst.     
      apply: Cl_Safety. 
  Qed. 
  
  
  (*****************************************************************************)

  
  (*****************************************************************************)
  (** *Dense closure operator *)
  (*****************************************************************************)
  
  Definition Dense (π: prop): Prop :=
    forall t, finite t -> π t.

  Definition dCl : prop -> prop :=
    fun π => (fun t => finite t \/ π t).

  Lemma Dense_dCl (π: prop): Dense (dCl π).
  Proof. firstorder. Qed.


  Lemma dCl_mono : monotone dCl.
  Proof.
    move => π1 π2 sub t1. rewrite /dCl.
    move => [K1 | K2]; [by left | right; by apply: sub].   
  Qed.

  Lemma dCl_idmp : idempotent dCl.
  Proof.
    rewrite /dCl => π.
    apply: functional_extensionality => t.
    apply: prop_extensionality.
    firstorder. 
  Qed.

  Lemma dCl_ext : extensive dCl.
  Proof.  
    rewrite /dCl => π t π_t. by right.
  Qed.

  Lemma dCl_id_on_Dense  (π: prop):
    Dense π -> dCl π = π.
  Proof.
    rewrite /Dense /dCl => H_dense.
    apply: functional_extensionality => t. 
    apply: prop_extensionality. 
    split; auto. move => [k | k]; [by apply: H_dense | by []]. 
  Qed. 
  
  Definition dense_uco := Build_Uco dCl_mono
                                    dCl_idmp
                                    dCl_ext.

  
  Lemma Dense_Cl_prop :
  Dense = (lift (uco dense_uco)) h_true. 
  Proof.
    apply: functional_extensionality => π.
    apply: prop_extensionality.
    split; rewrite /h_true //= => H.
    + exists π. split; auto. by rewrite dCl_id_on_Dense.
    + destruct H as [b [Heq H]]. subst.
        by apply: Dense_dCl.
  Qed.
 
  (*****************************************************************************)
  
 

  Definition SSC  (H: hprop)  : Prop :=
    forall h, H h ->
         (forall b : prop, b ⊆ h -> H b).

  (*****************************************************************************)
  (** *SSC closure operator*)
  (*****************************************************************************)
  
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


End Properties.