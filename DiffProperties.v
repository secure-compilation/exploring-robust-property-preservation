From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Require Import DiffEvents.
Require Import DiffTraceModel.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.

Definition prop {k : level} := @trace k -> Prop.
Definition fprop {k : level} := @finpref k -> Prop. 

Notation "π1 ⊆ π2" := (forall t, π1 t -> π2 t) (at level 50).

Notation "M <<< b" := (forall m, M m -> exists t, b t /\ prefix m t) (at level 50).  

Definition Safety {k : level} (π : @prop k) : Prop :=
  forall t, ~ π t ->
       (exists m, prefix m t /\
             (forall t', prefix m t' -> ~ π t')).

Inductive Observations {k : level} : (@finpref k -> Prop) -> Prop :=
  empty :  Observations (fun m : finpref => False)
| finite_union : forall M m, Observations M -> Observations (fun x => M x \/ x = m).

          
(* CA: for now this is axiomatized but we can recover it by modifying
       results from TraceTopology.v *)
Definition Cl {k: level} (π : @prop k) : @prop k :=
  fun t => forall S, Safety S -> π ⊆ S -> S t.   
  
Lemma Cl_bigger {k: level} (π: @prop k) : π ⊆ (Cl π). 
Proof. firstorder. Qed. 

Lemma Cl_Safety {k: level} (π: @prop k): Safety (@Cl k π).
Proof.
  move => t not_π_t.
  move/not_forall_ex_not: not_π_t. move => [π' H].
  move/not_imp: H. move => [safety_π' H].
  move/not_imp: H. move => [π_leq_π' not_π'_t].
  destruct (safety_π' t not_π'_t) as [m [m_leq_t m_wit]].
  exists m. split; auto. move => t' m_leq_t' Hf.
  apply: (m_wit t'). assumption. by apply: Hf. 
Qed.

Require Import FunctionalExtensionality.

Hypothesis prop_extensionality : forall A B:Prop, (A <-> B) -> A = B. 

Lemma Cl_id_on_Safe {k: level} (π: @prop k): Safety π -> Cl π = π.
Proof.
  move => Safety_π. apply: functional_extensionality => t.
  apply: prop_extensionality.
  by firstorder. 
Qed.  
 
Lemma Cl_smallest {k: level} (π :@prop k) : forall S, @Safety k S -> π ⊆ S -> Cl π ⊆ S.
Proof. by firstorder. Qed. 

Definition hprop {k : level} := @prop k -> Prop.

Definition SSC {k: level} (H: @hprop k)  : Prop :=
  forall h, H h ->
       (forall b : prop, b ⊆ h -> H b).

Definition sCl {k : level} (H : @hprop k) : @hprop k :=
  fun b => exists b', H b' /\ b ⊆ b'.

Lemma sCl_bigger {k : level} (H : @hprop k) : H ⊆ (sCl H). 
Proof. firstorder. Qed.   
  
Lemma sCl_SCH {k : level} (H : @hprop k) : SSC (sCl H).
Proof.
  move => h [b' [Hb' bb']] b b_h. exists b'; auto.
Qed.

Lemma sCl_id_on_SSC {k: level} (H: @hprop k): SSC H -> sCl H = H.
Proof.
  move => H_SSC. apply: functional_extensionality => b.
  apply: prop_extensionality. firstorder. 
Qed.

Lemma sCl_smallest {k : level} (H: @hprop k):
  forall H', SSC H' -> H ⊆ H' -> (sCl H) ⊆ H'.
Proof.
  move => H' ssc_H' H_leq_H' b [b' [ b_leq_b' H_b']].
  apply: (ssc_H' b'); auto.
Qed.   
  
Definition HSafe {k : level} (H: @hprop k) :=
  forall b, ~ H b -> (exists M, Observations M /\ M <<< b /\
                     (forall b', M <<< b' -> ~ H b')). 

Definition hsCl {k : level} (H: @hprop k): @hprop k :=
  fun b => forall Hs, HSafe Hs -> H ⊆ Hs -> Hs b. 
  
Lemma hsCl_bigger {k : level} (H: @hprop k): H ⊆ hsCl H.
Proof. by firstorder. Qed. 

Lemma hsCl_HSafe {k: level} (H: @hprop k): HSafe (hsCl H). 
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
  
Lemma HSafe_SCH {k: level} : forall (H: @hprop k), HSafe H -> SSC H.
Proof. 
  move => H HSafe_H b Hb b' b'_leq_b. 
  apply: NNPP => not_H_b'.
  destruct (HSafe_H b' not_H_b') as [M [obs_M [M_leq_b' M_wit]]].
  apply: (M_wit b); firstorder. 
Qed. 
  
Lemma sCl_id_on_HSafe {k: level} : forall (H: @hprop k), HSafe H -> sCl H = H.
Proof.
  move => H HSafe_H.
  have SSC_H: (SSC H) by apply: HSafe_SCH.
  by rewrite (sCl_id_on_SSC SSC_H). 
Qed.   
  
Lemma hsCl_sCl {k : level} : forall (H: @hprop k), sCl H ⊆ hsCl H.  
Proof.
  move => H.
  have ssc: SSC (hsCl H).
  { apply: HSafe_SCH. apply: hsCl_HSafe. }
  apply: sCl_smallest; auto.
    by apply: hsCl_bigger.
Qed.

Lemma hsCl_smallest {k : level} (H: @hprop k):
  forall H', HSafe H' -> H ⊆ H' -> (hsCl H) ⊆ H'.
Proof. by firstorder. Qed.


Definition Dense {k: level} (π: @prop k): Prop :=
  forall t, finite t -> π t.

Definition dCl {l: level} : @prop l -> @prop l :=
  fun π => (fun t => finite t \/ π t).

Lemma Dense_dCl {l: level} (π: @prop l): Dense (dCl π).
Proof. firstorder. Qed.
