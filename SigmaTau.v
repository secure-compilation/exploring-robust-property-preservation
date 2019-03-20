From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Require Import DiffEvents.
Require Import DiffTraceModel.
Require Import DiffProperties.
Require Import DiffCommonST.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.

Definition σRP (σ : @prop target -> @prop source)
           (P : par src) (π : @prop target) :=
   rsat P (σ π) -> rsat (P↓) π.

Definition σRTP (σ : @prop target -> @prop source) :=
  forall (P : par src) (π : @prop target), σRP (σ) P π. 

Definition τRP (τ : @prop source -> @prop target)
               (P : par src) (π : @prop source) :=
  rsat P  π -> rsat (P↓) (τ π).

Definition τRTP (τ : @prop source -> @prop target) :=
  forall (P : par src) (π : @prop source), τRP (τ) P π. 

Lemma contra_τRP (τ : @prop source -> @prop target)
                 (P : par src) (π : @prop source) :
  τRP τ P π <-> ((exists Ct t, sem (plug (P↓) Ct) t /\ ~ (τ π) t) ->
               (exists Cs s, sem (plug P Cs) s /\ ~ π s)).
Proof.
 unfold τRP. by rewrite [_ -> _] contra !neg_rsat. 
Qed.

Lemma contra_τRTP (τ : @prop source -> @prop target) :
  τRTP τ <-> ( forall (P : par src) (π : @prop source),
               (exists Ct t, sem (plug (P↓) Ct) t /\ ~ (τ π) t) ->
               (exists Cs s, sem (plug P Cs) s /\ ~ π s)).
Proof.
 unfold τRTP. split => H P π; move: (H P π); by rewrite -contra_τRP.   
Qed. 

Lemma contra_σRP (σ : @prop target -> @prop source)
                  (P : par src) (π : @prop target) :
  σRP σ P π <-> ((exists Ct t, sem (plug (P↓) Ct) t /\ ~ π t) ->
               (exists Cs s, sem (plug P Cs) s /\ ~ (σ π) s)).
Proof.   
  unfold σRP. by rewrite [_ -> _] contra !neg_rsat.
Qed.
  
Variable rel : @trace source -> @trace target -> Prop. 

Definition tilde_RTC := forall P Ct (t : @trace target),
    sem (plug (P ↓) Ct) t ->
    (exists Cs s, rel s t /\ sem (plug P Cs) s).

Definition τ' : @prop source -> @prop target :=
  fun π => (fun t => exists s, π s /\ rel s t).  

Definition σ' : @prop target -> @prop source :=
  fun π => (fun s => exists t, π t /\ rel s t). 


Theorem tilde_RTC_τRTP : tilde_RTC <-> τRTP (τ').
Proof.
  rewrite contra_τRTP. split.    
  - move => Htilde P π [Ct [t [Hsemt Hτ]]].
    destruct (Htilde P Ct t Hsemt) as [Cs [s [Hrel_s_t Hsems]]].   
    exists Cs, s. split; auto. move => s_in_π. apply: Hτ. by exists s.
 - move => Hτ P Ct t Hsemt. specialize (Hτ P (fun s => ~ rel s t)).
   case: Hτ.
   { exists Ct, t. split; auto. unfold τ'. move => [s [Hc Hcc]] //=. }
   move  => Cs [s [Hsems H]]. exists Cs, s. split; auto; by apply: NNPP.                                  
Qed.

Lemma rsat_upper_closed {k : level} {K : @language k}:
  forall (P : par K) (π1 π2 : @prop k), rsat P π1 -> π1 ⊆ π2 -> rsat P π2.  
Proof.  
  move => P π1 π2 Hrsat1 Hsuper C t Hsem. apply: Hsuper.
  by apply: (Hrsat1 C t).  
Qed. 

(*CA: I never use the monotonicity but suspect it is for free *)
Definition Galois_fst (σ : @prop target -> @prop source)
                      (τ : @prop source -> @prop target) : Prop :=

  (forall (πs : @prop source), πs ⊆ σ (τ πs)).

Definition Galois_snd (σ : @prop target -> @prop source)
                      (τ : @prop source -> @prop target) : Prop :=
  (forall (πt : @prop target), τ (σ πt) ⊆ πt).

Definition Galois_cp  (σ : @prop target -> @prop source)
                      (τ : @prop source -> @prop target) : Prop :=
  Galois_fst σ τ /\ Galois_snd σ τ. 

Theorem σ_τ_equiv (σ : @prop target -> @prop source)
                  (τ : @prop source -> @prop target) :
  (Galois_cp σ τ) -> (σRTP σ) <-> (τRTP τ).
Proof.
  move => [G1 G2]. split. 
  - move => Hσ P πs Hrsat_src. apply: (Hσ P (τ πs)).
    apply: (rsat_upper_closed Hrsat_src). by apply: G1. 
  - move => Hτ P πt Hrsat_tgt.
    have H : rsat (P ↓) (τ (σ πt)) by apply: Hτ. 
    apply: (rsat_upper_closed H). by apply: G2.
Qed.

Corollary all_equivalent : (Galois_cp σ' τ') ->
                                   σRTP (σ') <-> tilde_RTC.
Proof. move => G. by rewrite tilde_RTC_τRTP (σ_τ_equiv G). Qed. 

(* We actually need need only Galois_snd to have the equivalence *)

Lemma Galois_fst_holds : (forall s, exists t, rel s t) -> Galois_fst σ' τ'.
Proof.
  move => Hrel πs s Hπs. unfold σ', τ'.
  destruct (Hrel s) as [t Hrel_s].  
  exists t. split; auto. now exists s.
Qed.

Definition total_rel (r : @trace source -> @trace target -> Prop) :=
  forall s, exists t, rel s t. 

Lemma Galois_implies_total_rel :
  Galois_cp σ' τ' -> (total_rel rel).
Proof.
  move => [G1 G2] s.
  have Hs: (σ' (τ' (fun s' => s' = s))) s by apply: G1.   
  destruct Hs as [t Hs]. now exists t.
Qed.

(******************************************************************************)
(** *Safety *)
(******************************************************************************)

Definition tilde_RSC :=
  forall P Ct (t : @trace target) (m : @finpref target),
   prefix m t -> sem (plug (P ↓) Ct) t ->
   (exists Cs t' s, rel s t' /\ prefix m t' /\ sem (plug P Cs) s).

Notation "f ∘ g" := (fun t => f (g t)) (at level 50).

Theorem tilde_RSC_σRSP :
  (total_rel rel) ->
  (forall πt, @Safety target πt -> (τ' (σ' πt) ⊆ πt)) ->
  ( tilde_RSC <->
  (forall P (π : @prop target), Safety π -> σRP σ' P π)). 
Proof.
  move => Htotal_rel G2_forSafety. 
  split. 
  - move => Htilde P π HSafety. rewrite contra_σRP.
    move => [Ct [t [Hsemt Hnot_t]]].  
    destruct (HSafety t Hnot_t) as [m [Hpref_m_t m_witness]]. 
    destruct (Htilde P Ct t m) as [Cs [t' [s [Hrel_s_t' [Hpref_m_t' Hsem_s]]]]]; auto. 
    exists Cs, s. split; auto => Hσs. 
    have Ht0 : π t'.
    { apply: G2_forSafety; auto. now exists s. }    
    by apply: (m_witness t').
  - move => H_RSP P Ct t m Hpref_m_t Hsemt.
    have HSafetyπ : @Safety target (fun t' => ~ prefix m t').
    { move => t'. rewrite -dne => prefix_m_t'.
      now exists m. }
    move : (H_RSP P (fun t' => ~ prefix m t') HSafetyπ).
    rewrite contra_σRP => Himp. destruct Himp as [Cs [s [Hsem_s Hσ]]].
    now exists Ct, t.
    unfold σ' in Hσ.
    have Ht_s : exists t', rel s t' /\ prefix m t'.
    { destruct (Htotal_rel s) as [t' Hrel_s_t']. 
      exists t'. split; auto. apply: NNPP => Hf. apply: Hσ.
      now exists t'. } 
    destruct Ht_s as [t' [Hpref' Hrel']].  
    exists Cs, t', s. split; auto.
Qed.


Theorem tilde_RSC_τRSP :
  (total_rel rel) ->
  (forall πt, @Safety target πt -> ((@Cl target ∘ τ') ((@Cl source ∘ σ') (πt)) ⊆ πt)) ->
  tilde_RSC <->
  (forall P (π : @prop source), Safety π -> τRP (Cl ∘ τ') P π).
Proof.
  move => Htotal_rel G2_with_Cl.
  split.
  - move => Htilde P π HSafetyπ. rewrite contra_τRP. move => [Ct [t [Hsemt H_not_π_t]]]. 
    have HSafety_Cl : Safety (Cl (τ' π)) by apply: Cl_Safety.
    destruct (HSafety_Cl t) as [m [Hpref_m_t m_witness]]; auto.
    destruct (Htilde P Ct t m) as [Cs [t' [s [Hrel_s_t' [Hpref_m_t' Hsem_s]]]]]; auto.  
    exists Cs, s. split; auto => π_s. 
    have Hτ_t' : Cl (τ' π) t'.
    { apply: Cl_bigger. now exists s. }
      by apply: (m_witness t').
  - move => Hτ P Ct t m Hpref_m_t Hsem_t.
    have HSafety_π : Safety (fun t' => ~ prefix m t').
    { move => t'. rewrite -dne => Hpref. now exists m. }  
    specialize (G2_with_Cl (fun t' => ~ prefix m t') HSafety_π).
    have HSafety_Cl : Safety ((Cl ∘ σ') ((fun t' => ~ prefix m t'))) by apply: Cl_Safety. 
    move: (Hτ P ((Cl ∘ σ') ((fun t' => ~ prefix m t'))) HSafety_Cl).
    rewrite contra_τRP => Himp. destruct Himp as [Cs [s [Hsem_s HCl]]].
    { exists Ct, t. split; auto. by move/G2_with_Cl => H. } 
    destruct (Htotal_rel s) as [t' Hrel_s_t'].
    have Ht' : prefix m t'.
    { have : ~ (σ' (not ∘ prefix m)) s. by move/Cl_bigger => H.
      unfold σ'. rewrite not_ex_forall_not. move => H.
      move: (H t'). rewrite de_morgan1 -dne. firstorder. }
    now exists Cs, t', s.
Qed.
    