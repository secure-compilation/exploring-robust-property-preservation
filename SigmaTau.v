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

Definition Adjunction_law  (σ : @prop target -> @prop source)
                           (τ : @prop source -> @prop target) : Prop := 

  forall (π__s :@prop source) (π__t : @prop target),
          (τ π__s) ⊆ π__t <-> π__s ⊆ (σ π__t).

Definition monotone {l1 l2 : level} (f : @prop l1 -> @prop l2) : Prop :=
  forall π1 π2: @prop l1, (π1 ⊆ π2) -> (f π1 ⊆ f π2). 

Lemma prop_subset_trans {l : level} (π1 π2 π3: @prop l) :
  π1 ⊆ π2 -> π2 ⊆ π3 -> π1 ⊆ π3.
Proof. by firstorder. Qed.

Lemma hprop_subset_trans {l : level} (π1 π2 π3: @hprop l) :
  π1 ⊆ π2 -> π2 ⊆ π3 -> π1 ⊆ π3.
Proof. by firstorder. Qed.

Lemma Galois_equiv  (σ : @prop target -> @prop source)
                    (τ : @prop source -> @prop target) : 

  Adjunction_law σ τ <-> ( monotone σ /\ monotone τ /\ Galois_cp σ τ). 
Proof.
  split.
  - move => H_adj. split.
    + move => π1 π2 H_sub. rewrite -(H_adj (σ π1) π2). 
      have H_π1 : τ (σ π1) ⊆ π1 by rewrite H_adj. 
      by apply: (prop_subset_trans H_π1).      
    + split.
      ++ move => π1 π2 H_sub.  rewrite (H_adj π1 (τ π2)).
         have H_π2 : π2 ⊆  (σ (τ π2)) by rewrite -H_adj.
         by apply: (prop_subset_trans H_sub H_π2).
      ++ split; move => π; [by rewrite -H_adj | by rewrite H_adj].         
  - move => [sigma_mon [tau_mon [G1 G2]]] πs πt.  
    split => H.
    + apply: (prop_subset_trans (G1 πs)).
      by apply: (sigma_mon (τ πs) πt H).
    + apply: (prop_subset_trans (tau_mon πs (σ πt) H)).
      by apply G2.
Qed.         
         
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

Corollary tilde_RTC_σRTP : total_rel rel ->
                           Galois_snd σ' τ' ->
                           σRTP (σ') <-> tilde_RTC.
Proof. move => H_rel G2.
       have: Galois_cp σ' τ'. { split; auto. by apply: Galois_fst_holds. }
       exact all_equivalent.
Qed.        

Lemma τ'_preserves_joins (H: @hprop source): forall t: @trace target,

      (τ' (fun s => exists b, H b /\ b s)) t <-> (fun x => exists b, H b /\ (τ' b) x) t.     
Proof. by firstorder. Qed.

Lemma τ'_meets (H: @hprop source): forall t: @trace target,

    (τ' (fun s => forall b, H b -> b s)) t -> (fun x => forall b, H b -> (τ' b) x) t.
Proof. by firstorder. Qed. (* TODO: check if the equivalence holds *)


(* σ' is not necessarely the upper adjoint of τ', 
   we now define γ' and later show it is the upper adjoint
 *)

Definition γ' : @prop target -> @prop source :=
  fun π__t => (fun t__s: @trace source => forall t__T : @trace target, rel t__s t__T -> π__t t__T).  

Lemma γ'_upper_adjoint_τ' : Adjunction_law γ' τ'.
Proof.
  move => π__S π__T. split => H.
  - move => t__S π_t__S t__T H_rel.
    have τ'_t__T : (τ' π__S) t__T by exists t__S. 
    exact (H t__T τ'_t__T).   
  - move => t__T [t__S [π_t__S H_rel]].
    move: (H t__S π_t__S). firstorder.
Qed.     

Lemma τRTP_γRTP : τRTP τ' <-> σRTP γ'.
Proof. 
  rewrite (@σ_τ_equiv γ' τ'). reflexivity.  
  have: Adjunction_law γ' τ' by apply: γ'_upper_adjoint_τ'. 
  now rewrite Galois_equiv.
Qed. 

(*CA: using the proper upper adjoint we don't need any hypothesis to show 
      this equivalence  
 *)
Theorem tilde_RTC_γRTP : tilde_RTC <-> σRTP γ'.
Proof. by rewrite -τRTP_γRTP tilde_RTC_τRTP. Qed.  


Section σ'_upper_adjoint.
(*CA: when γ' = σ'? *)

Require Import FunctionalExtensionality.

Hypothesis prop_extensionality : forall A B:Prop, (A <-> B) -> A = B.

Lemma sufficient_condition_γ'_eq_σ' :                                    
  (forall t__S, exists! t__T, rel t__S t__T) -> γ' = σ'. 
Proof.
  move => H. apply: functional_extensionality => π__t.
  apply: functional_extensionality => t__S. 
  rewrite /γ' /σ'.
  apply: prop_extensionality. split.
  - by firstorder.
  - move => [t__T [πt_tT rel_ts_tt]] t__T' H'.
    destruct (H t__S) as [t Ht].
    have: t = t__T by apply Ht.
    have: t = t__T' by apply Ht. by move => foo1 foo2; subst.
Qed.

Lemma necessary_condition_γ'_eq_σ' :
  γ' = σ' ->  (forall t__S, exists! t__T, rel t__S t__T).
Proof.
  move => H_eq t__S.
  have [G1 G2]: Galois_cp σ' τ'.
  { rewrite -H_eq.
    have: Adjunction_law γ' τ' by apply: γ'_upper_adjoint_τ'.
    rewrite Galois_equiv. by firstorder. } 
  have: exists t__T, rel t__S t__T by apply: Galois_implies_total_rel.   
  move => [t__T rel_s_t].
  exists t__T. split; auto. move => t__T' rel_s_t'.
  have H: τ' (σ' (eq t__T)) t__T'.
  { exists t__S. split;auto. by exists t__T. }
  by apply: (G2 (eq t__T) t__T' H).
Qed. 

(*CA: we show γ' = σ', we should also show that τ' uniquely defines its upper adjoint
      but this is a well known fact
   *)

Theorem σ'_τ'_adjoint_iff :
  γ' = σ' <->  (forall t__S, exists! t__T, rel t__S t__T).
Proof.
  split. apply: necessary_condition_γ'_eq_σ'.
  apply: sufficient_condition_γ'_eq_σ'.
Qed.   

(*CA: all theorems in which γ' is used holds for σ' by just assuming 
      rel is a total function : @trace source -> @trace target *)

End σ'_upper_adjoint.   

(******************************************************************************)
(** *Safety *)
(******************************************************************************)

Definition tilde_RSC :=
  forall P Ct (t : @trace target) (m : @finpref target),
   prefix m t -> sem (plug (P ↓) Ct) t ->
   (exists Cs t' s, rel s t' /\ prefix m t' /\ sem (plug P Cs) s).

Lemma tilde_RTC_tilde_RSC : tilde_RTC -> tilde_RSC.
Proof.
  move => H_tilde P Ct t m m_leq_t H_t. 
  move: (H_tilde P Ct t H_t). firstorder. 
Qed. 
  
Notation "f ∘ g" := (fun t => f (g t)) (at level 100).

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

(*CA: using the proper upper adjoint we don't need any hypothesis to show 
      this equivalence  
 *)
Theorem tilde_RSC_γRSP :
  ( tilde_RSC <->
  (forall P (π : @prop target), Safety π -> σRP γ' P π)).
Proof.
  have H_adj: Adjunction_law γ' τ' by apply γ'_upper_adjoint_τ'. 
  have G2 : Galois_snd γ' τ' by firstorder.
  split.
  - move => Htilde P π HSafety. rewrite contra_σRP.
    move => [Ct [t [Hsemt Hnot_t]]].  
    destruct (HSafety t Hnot_t) as [m [Hpref_m_t m_witness]]. 
    destruct (Htilde P Ct t m) as [Cs [t' [s [Hrel_s_t' [Hpref_m_t' Hsem_s]]]]]; auto. 
    exists Cs, s. split; auto => Hσs. 
    have Ht0 : π t'.
    { apply: G2; auto. now exists s. }    
    by apply: (m_witness t').
  - move => H_RSP P Ct t m Hpref_m_t Hsemt.
    have HSafetyπ : @Safety target (fun t' => ~ prefix m t').
    { move => t'. rewrite -dne => prefix_m_t'.
      now exists m. } 
    move : (H_RSP P (fun t' => ~ prefix m t') HSafetyπ).
    rewrite contra_σRP => Himp. destruct Himp as [Cs [s [Hsem_s Hσ]]].
    now exists Ct, t. 
    have : ~ (fun s':@trace source => s' = s) ⊆ (γ' (not ∘ prefix m)) by firstorder.
    rewrite -H_adj not_forall_ex_not. move => [t' Ht'].
    move/not_imp: Ht' => [Ht' HHt'].
    exists Cs, t', s. repeat (split; auto).
    destruct Ht' as [s' [Heq Hs']]. by subst.   
      by apply: NNPP.
Qed.       
 
      

Theorem tilde_RSC_τRSP :
  (forall πt, @Safety target πt -> (@Cl target ∘ τ') ((@Cl source ∘ γ') (πt)) ⊆ πt) ->
  tilde_RSC <->
  (forall P (π : @prop source), Safety π -> τRP (Cl ∘ τ') P π).
Proof.
  have H_adj : Adjunction_law γ' τ' by apply: γ'_upper_adjoint_τ'. 
  move => G2_with_Cl.
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
    have HSafety_Cl : Safety ((Cl ∘ γ') ((fun t' => ~ prefix m t'))) by apply: Cl_Safety. 
    move: (Hτ P ((Cl ∘ γ') ((fun t' => ~ prefix m t'))) HSafety_Cl).
    rewrite contra_τRP => Himp. destruct Himp as [Cs [s [Hsem_s HCl]]].
    { exists Ct, t. split; auto. by move/G2_with_Cl => H. }
    have γ'_not_s: ~ (γ' (not ∘ prefix m)) s.
    { move => Hf. apply: HCl. by apply: Cl_bigger. }
     have : ~ (fun s':@trace source => s' = s) ⊆ (γ' (not ∘ prefix m)) by firstorder.
    rewrite -H_adj not_forall_ex_not. move => [t' Ht'].
    move/not_imp: Ht' => [Ht' HHt'].
     exists Cs, t', s. repeat (split; auto).
    destruct Ht' as [s' [Heq Hs']]. by subst.   
      by apply: NNPP.
Qed.


(* CA: we try to impose conditions on rel to get the equivalence tilde_RSC_τRSP *)
Definition src_obs_rel (R: @trace source -> @trace target -> Prop) : Prop :=
  forall t__S t__T, R t__S t__T ->  (exists m__S,  prefix m__S t__S /\
                                 forall t__S', prefix m__S t__S' -> rel t__S' t__T). 

Lemma γ'_maps_Safety_to_Safety :
  src_obs_rel rel ->
  forall π__T, @Safety target π__T -> @Safety source (γ' π__T). 
Proof.
  move => Hrel π__T Safety__T t__S not_t__S.
  move/not_forall_ex_not : not_t__S. move => [t__T H].
  move/not_imp : H. move => [s_rel_t not_t__T].
  destruct (Hrel t__S t__T s_rel_t) as [m__S [pref_s  H_obs]]. 
  exists m__S. split; auto.
Qed.

Lemma G2_Safety :
  src_obs_rel rel ->
  (forall πt, @Safety target πt -> (@Cl target ∘ τ') ((@Cl source ∘ γ') (πt)) ⊆ πt).
Proof.
  move => H_rel. move/γ'_maps_Safety_to_Safety : H_rel.
  move => H_Safety π__T Safety__T. specialize (H_Safety π__T Safety__T). 
  rewrite (Cl_id_on_Safe H_Safety). apply: Cl_smallest; auto. 
  have G2 : Galois_snd γ' τ'.
  { have H_adj : Adjunction_law γ' τ' by apply: γ'_upper_adjoint_τ'.
    firstorder. }     
    by apply: G2.
Qed.

Theorem tilde_RSC_τRSP_hp_on_tilde :
  src_obs_rel rel ->
   tilde_RSC <->
   (forall P (π : @prop source), Safety π -> τRP (Cl ∘ τ') P π).
Proof.
  move => H_src. rewrite tilde_RSC_τRSP.
  reflexivity.
  by apply: G2_Safety.
Qed. 

(*CA: Without the hp src_obs_rel tilde_RSC is equivalent to 
      the (Cl ∘ τ') robust preservation of *arbitrary* source properties 
  *)
Theorem tilde_RSC_τRTP :
  tilde_RSC <->
  (forall P (π : @prop source), τRP (Cl ∘ τ') P π).
Proof.
  have H_adj : Adjunction_law γ' τ' by apply: γ'_upper_adjoint_τ'. 
  split.
  - move => Htilde P π. rewrite contra_τRP. move => [Ct [t [Hsemt H_not_π_t]]]. 
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
    move: (Hτ P (γ' ((fun t' => ~ prefix m t')))).
    rewrite contra_τRP => Himp. destruct Himp as [Cs [s [Hsem_s HCl]]].
    { exists Ct, t. split; auto. move => Hf.
      have adj_cons: Cl (τ' (γ' (not ∘ prefix m))) ⊆ (not ∘ prefix m). 
      { apply: Cl_smallest. assumption.
        move/Galois_equiv : H_adj; firstorder. } 
      by apply: (adj_cons t). } 
    move/not_forall_ex_not: HCl. move => [t' HH].
    move/not_imp: HH => [rel_s_t' nn_prefix]. 
    exists Cs, t', s. repeat (split; auto).
      by apply: NNPP.
Qed.       
    
(******************************************************************************)
(** *Subset-Closed *)
(******************************************************************************)

Lemma rhsat_upper_closed {k : level} {K : @language k}:
  forall (P : par K) (H1 H2 : @hprop k), rhsat P H1 -> H1 ⊆ H2 -> rhsat P H2.  
Proof. by firstorder. Qed. 

Definition tilde_RSCHC :=
  forall P Ct, exists Cs,
      (forall t, sem (plug (P↓) Ct) t -> (exists s, rel s t /\ sem (plug P Cs) s)).

Lemma tilde_RSCHC_tilde_RTC : tilde_RSCHC -> tilde_RTC.
Proof.
  move => Htilde P Ct t H_t. move: (Htilde P Ct). firstorder.
Qed. 

Definition lift {l1 l2 : level} (f : @prop l1 -> @prop l2) (H : @hprop l1) : @hprop l2 :=
  fun (b1 : @prop l2) => exists b2, (H b2) /\ b1 = f b2. 

Definition σRhP (hσ : @hprop target -> @hprop source)
                (P : par src) (H : @hprop target) :=
  rhsat P (hσ H) -> rhsat (P↓) H.

Definition τRhP (hτ : @hprop source -> @hprop target) 
                (P : par src) (H : @hprop source) :=
  rhsat P H -> rhsat (P↓) (hτ H).
 
Check (lift τ').
Check sCl.
Check (sCl ∘ (lift τ')).

Lemma Galois_fst_SSCH  (σ : @prop target -> @prop source)
                       (τ : @prop source -> @prop target) :
  Adjunction_law σ τ ->
  (forall H : @hprop target, SSC H -> (sCl ∘ (lift τ)) ((sCl ∘ (lift σ)) H) ⊆ H). 
Proof.
  move => H_adj H H_ssc b τ_σ_H_b.  
  unfold sCl, lift in τ_σ_H_b. 
  destruct τ_σ_H_b as [b' [[b2 [cond b'_eq]] b_b']]. subst. 
  destruct cond as [b' [[b2' [H_b2' b'_eq]] b2_b']]. subst.  
  move/H_adj: b2_b' => b2_b'. have b_b2': b ⊆ b2' by firstorder.     
  by apply: (H_ssc b2'). 
Qed.

Lemma Galois_snd_SSCH  (σ : @prop target -> @prop source)
                       (τ : @prop source -> @prop target) :
  Adjunction_law σ τ ->
  (forall H : @hprop source, SSC H -> H ⊆ (sCl ∘ (lift σ)) ((sCl ∘ (lift τ)) H)).
Proof.
   move => H_adj H H_ssc b H_b.  
   unfold sCl, lift. exists (σ (τ b)). split.
   - exists (τ b). split; auto.
     + exists (τ b). split; auto.
       ++ by exists b.   
     + move/Galois_equiv: H_adj. move => [H_mono1 [H_mono2 [G1 G2]]]. 
       apply: G1. 
Qed.

Theorem τRSCHP_σRSCHP  (σ : @prop target -> @prop source)
                       (τ : @prop source -> @prop target) :
  Adjunction_law σ τ ->
  ((forall P (H: @hprop target), SSC H ->  σRhP (sCl ∘ (lift σ)) P H) <->
   (forall P (H: @hprop source), SSC H ->  τRhP (sCl ∘ (lift τ)) P H)).
Proof.
  move => H_adj. split.
  - move => Hσ P H H_ssc rsat_source. 
    have rsat_sigma_tau : rhsat P ((sCl ∘ (lift σ)) ((sCl ∘ (lift τ)) H)).  
    { apply: rhsat_upper_closed. exact rsat_source.
      by apply: Galois_snd_SSCH. }       
    have τ_ssc : SSC (sCl ((lift τ) H)) by apply: sCl_SCH.
    exact (Hσ P ((sCl ((lift τ) H))) τ_ssc rsat_sigma_tau).  
  - move => Hτ P H H_ssc rsat_source.
    have h_ssc: SSC ((sCl ∘ lift σ) H) by apply: sCl_SCH.
    move: (Hτ P ((sCl ∘ lift σ) H) h_ssc rsat_source).
    move => HHH. eapply rhsat_upper_closed. exact HHH.
    by apply: Galois_fst_SSCH.
Qed.       

Corollary τRSCHP_γRSCHP :
   (forall P (H: @hprop target), SSC H ->  σRhP (sCl ∘ (lift γ')) P H) <->
   (forall P (H: @hprop source), SSC H ->  τRhP (sCl ∘ (lift τ')) P H).
Proof.
  rewrite τRSCHP_σRSCHP. reflexivity.
    by apply: γ'_upper_adjoint_τ'.
Qed.     

Theorem tilde_RSCHC_τRSCHP :
  tilde_RSCHC <-> (forall P (H: @hprop source), SSC H ->  τRhP (sCl ∘ (lift τ')) P H). 
Proof.
  split. 
  - move => Htilde P H H_ssc. rewrite /τRhP contra !neg_rhsat.
    move => [Ct Hsem].
    move: (Htilde P Ct) => [Cs HH]. exists Cs => Hfalse.
    apply: Hsem. 
    exists (τ' (beh (plug P Cs))). split.
    + by exists (beh (plug P Cs)). 
    + move => t Ht. destruct (HH t Ht) as [s [Hs1 Hs2]]. now exists s.
  - move => Hτ P Ct.
    have Hssc : SSC (fun b: @prop source =>  ~ beh(plug (P↓) Ct) ⊆ τ' b).
    { move => b1 Hb1 b2 b1_b2 Hb2. apply: Hb1. firstorder. }    
    specialize (Hτ P (fun b: @prop source =>  ~ beh(plug (P↓) Ct) ⊆ τ' b) Hssc).
    apply contra in Hτ. move: Hτ. rewrite !neg_rhsat. 
    move => [Cs Hbeh]. move/NNPP: Hbeh. 
    exists Cs => t Hsem_t. move: (Hbeh t Hsem_t). firstorder.
    move => Hf. specialize (Hf Ct).
    destruct Hf as [b' [Hb' Hbb]]. destruct Hb' as [bs [Hbs1 Hbs2]]. now subst.  
Qed.

(* CA: looking also for a direct proof here we need the adjunction law,
        in particular we need monotonicity and Galois_cd *)
Theorem tilde_RSCHC_σRSCHP :
  Adjunction_law σ' τ' ->
  tilde_RSCHC <-> (forall P (H: @hprop target), SSC H ->  σRhP (sCl ∘ (lift σ')) P H).
Proof.
  move => H_adj. rewrite (τRSCHP_σRSCHP H_adj).
  move/Galois_equiv: H_adj => [mono_tau [mono_sigma [G1 G2]]].
  have h_rel : total_rel rel by apply: Galois_implies_total_rel. 
  by rewrite tilde_RSCHC_τRSCHP. 
Qed.

Corollary tilde_RSCHC_γRSCHP :
  tilde_RSCHC <-> (forall P (H: @hprop target), SSC H ->  σRhP (sCl ∘ (lift γ')) P H).
Proof. by rewrite τRSCHP_γRSCHP tilde_RSCHC_τRSCHP. Qed. 

(******************************************************************************)
(** *HyperSafety *)
(******************************************************************************)

Definition tilde_RHSC := forall P Ct (M : finpref -> Prop),
                            Observations M ->
                            M <<< (beh (plug (P↓) Ct)) ->
                            (exists Cs, forall m, M m -> exists t s, prefix m t /\ 
                                                            rel s t /\
                                                    beh (plug P Cs) s).

Lemma conclusion_RSHC (P : par src) (M : finpref -> Prop) (Cs : ctx src) :
  (forall m, M m -> exists t s, prefix m t /\ 
                                  rel s t /\
                                  beh (plug P Cs) s) <->
  M <<< τ' (beh (plug P Cs)).
Proof. firstorder. Qed.  

Lemma tilde_RSCHC_tilde_RHSC : tilde_RSCHC -> tilde_RHSC.
Proof.
  move => H_tilde P Ct M Obs_M H_M.
  destruct (H_tilde P Ct) as [Cs H_Cs].
  exists Cs => m M_m.
  destruct (H_M m M_m) as [t [H_t m_pref_t]].  
  destruct (H_Cs t H_t) as [s [rel_s_t H_s]]. now exists t, s.
Qed. 
                                                  
Lemma Galois_snd_HSafe  (σ : @prop target -> @prop source)
                        (τ : @prop source -> @prop target) :
  Adjunction_law σ τ ->
  (forall H : @hprop source, HSafe H -> H ⊆ (hsCl ∘ (lift σ)) ((hsCl ∘ (lift τ)) H)).
Proof.
  move => H_adj H H_HSafe bs H_bs.
  have HSafe_σ : HSafe ((hsCl ∘ lift σ) ((hsCl ∘ lift τ) H)) by apply: hsCl_HSafe. 
  rewrite -(sCl_id_on_HSafe HSafe_σ).
  exists (σ (τ bs)). split.
  + apply: hsCl_bigger. exists (τ bs). split; auto.
    have HSafe_τ : HSafe (hsCl (lift τ H)) by apply: hsCl_HSafe.
    rewrite -(sCl_id_on_HSafe HSafe_τ).
    exists (τ bs). split; auto. 
    apply hsCl_bigger. by exists bs. 
  + move/Galois_equiv: H_adj. move => [mono_sigma [mono_tau [G1 G2]]].
    by apply: G1.
Qed.


(* 
 CA: I do not think it is possible to prove
     Galois_fst_HSafe : 
      Adjunction_law σ τ ->
      (forall H : @hprop target, HSafe H -> (hsCl ∘ (lift τ)) ((hsCl ∘ (lift σ)) H) ⊆ H).

     Indeed hsCl is stronger than sCl meaning that 

     1) forall H, sCl H ⊆ hsCl H. // trivial by hypersafety being subset closed
     2) exists H, sCl H ≠ hsCl H as the following example shows 

        let t be an infinite e.g. t = 42^ω. 

        b := True \ { t }. 

        H := { b }. 

        sCl H = 2^b. 

        Claim: sCl H is not Hypersafety. 

        Proof. { t } ∉ (sCl H) but for every M <<< { t }, M is a *finite* collection
               
               of prefixes of t. Take the longest of them, say m, {m;tstop} ∈ (sCl H).
        Qed.  

   
  Consequences: we need a strong assumption to prove tilde_RHSC_τRHSP and tilde_RHSC_σRHSP

                that says that one of the laws of the Galois connection holds 
               
                between hypersafety hprops.
 
                (Notice that for SSC we only need such lwas to hold in the set of all props)
*)

                              
Theorem tilde_RHSC_τRHSP :
  (forall H: @hprop target, HSafe H -> (hsCl ∘ (lift τ')) ((hsCl ∘ (lift γ')) H) ⊆ H) ->
  tilde_RHSC <-> (forall P (H: @hprop source), HSafe H ->  τRhP (hsCl ∘ (lift τ')) P H).
Proof.
  have H_adj : Adjunction_law γ' τ' by apply: γ'_upper_adjoint_τ'. 
  move => Galois_fst_HSafe. 
  split.
  - move/Galois_snd_HSafe: H_adj => H_adj H_tilde P H H_HSafe.
    rewrite /τRhP contra !neg_rhsat.
    move => [Ct not_beh].
    have hsCl_τH : HSafe (hsCl (lift τ' H)) by apply: hsCl_HSafe. 
    destruct (hsCl_τH (beh (plug (P↓) Ct)) not_beh) as [M [Obs_M [M_leq_beh M_bad]]]. 
    destruct (H_tilde P Ct M) as [Cs H_tilde_Cs]; auto.
    exists Cs => beh_source.
    have τH_τbeh_src : (lift τ' H) (τ' (beh (plug P Cs))) by exists (beh (plug P Cs)).
    have M_le_τbeh_src : M <<< τ'(beh (plug P Cs)).
    { move => m. move: (H_tilde_Cs m). firstorder. }
    apply: (M_bad (τ' (beh (plug P Cs)))); auto. by apply: hsCl_bigger.
  - move => τ_pres P Ct M  Obs_M M_leq_beh_tgt.
    have σ_safe : HSafe ((hsCl ∘ (lift γ')) (fun b => ~ (M <<< b))) by apply: hsCl_HSafe. 
    move: (τ_pres P ( (hsCl ∘ (lift γ')) (fun b => ~ (M <<< b))) σ_safe).
    move/contra => HH. move: HH. rewrite !neg_rhsat => τ_pres_P.
    destruct τ_pres_P as [Cs src_beh].
    { exists Ct => H_false.
      have H_t_HSafe : HSafe (fun b => ~ M <<< b).
        { exists M. repeat (split; auto). by apply: NNPP. }   
          specialize (Galois_fst_HSafe (fun b => ~ M <<< b) H_t_HSafe).
          move/dne : M_leq_beh_tgt => M_leq_beh_tgt. apply: M_leq_beh_tgt.
            by apply: Galois_fst_HSafe.
    }
    have M_leq_τ_beh_src: M <<< (τ' (beh (plug P Cs))).
    { have src_subset : ~ sCl (lift γ' (fun b : prop => ~ M <<< b)) (beh (plug P Cs)).
      { move => Hfoo. by apply: (src_beh (hsCl_sCl Hfoo)). } 
      have  Hτ : ~ (sCl (fun b : prop => ~ M <<< b)) (τ' (beh (plug P Cs))).   
      { move => [bt [M_leq_bt H_bt]]. apply: src_subset.
        exists (γ' bt). split; [by exists bt | by rewrite -H_adj]. }
      apply: NNPP. move => Hf. apply: Hτ. by exists (τ' (beh (plug P Cs))). } 
    exists Cs => m M_m. destruct (M_leq_τ_beh_src m M_m) as [t [τt prefix_m_t]].
    move: τt. rewrite /τ'. move => [s [H_t rel_s_t]]. by exists t, s.    
Qed. 

Theorem tilde_RHSC_σRHSP :
  (Adjunction_law σ' τ') ->
   (forall H: @hprop target, HSafe H -> (hsCl ∘ (lift τ')) ((hsCl ∘ (lift σ')) H) ⊆ H) -> 
  tilde_RHSC <-> (forall P (H: @hprop target), HSafe H ->  σRhP (hsCl ∘ (lift σ')) P H).
Proof.
  move => H_adj Galois_fst_HSafe.
  split.
  - move => H_tilde P Ht Ht_HSafe. rewrite /σRhP contra !neg_rhsat.
    move => [Ct not_Ht_beh_tgt].
    destruct (Ht_HSafe _ not_Ht_beh_tgt) as [M [Obs_M [M_leq_beh_tgt bad_M]]]. 
    destruct (H_tilde P Ct M Obs_M) as [Cs H_src]; auto.
    exists Cs => σ_src.
    have τ_σ_beh_src: (hsCl (lift τ' (hsCl (lift σ' Ht)))) (τ' (beh (plug P Cs))).
    { apply: hsCl_bigger. by exists (beh (plug P Cs)). }
    have Ht_τ_beh_src: Ht (τ' (beh (plug  P Cs))).
    { by apply: Galois_fst_HSafe. }
    have M_let_τ_beh_src: M <<< τ' (beh (plug P Cs)).
    { move => m M_m. move: (H_src m M_m). firstorder. }
      by apply: (bad_M (τ' (beh (plug P Cs)))).
  - move => H_σ P Ct M Obs_M M_leq_beh_tgt.
    have Ht_HSafe: HSafe (fun bt => ~ M <<< bt).
    { exists M. repeat split; auto. by apply: NNPP. } 
    move: (H_σ P _ Ht_HSafe). clear H_σ. rewrite /σRhP => H_σ. 
    move/contra: H_σ. rewrite !neg_rhsat => H_σ.
    destruct H_σ as [Cs H_σ]. by exists Ct. 
    exists Cs.
    have H_σ1 : ~ (lift σ' (fun bt : prop => ~ M <<< bt)) (beh (plug P Cs))
      by move => HH; apply: H_σ; apply: hsCl_bigger. 
    have M_leq_τ_beh_src: M <<< (τ' (beh (plug P Cs))).
    { apply: NNPP => Hτ. apply: H_σ.
      have HSafe_foo : HSafe (hsCl (lift σ' (fun bt : prop => ~ M <<< bt))) by apply: hsCl_HSafe.
      rewrite -(sCl_id_on_HSafe HSafe_foo). exists (σ' (τ' (beh (plug P Cs)))).
      split.
      + apply: hsCl_bigger. by exists (τ' (beh (plug P Cs))).
      + move/Galois_equiv: H_adj. move => [mono_sigma [mono_tau [G1 G2]]].
        apply: G1. }
    firstorder.
Qed.

Lemma G2_HSafety_aux (H: @hprop target) : HSafe H ->  ((lift τ') ((sCl ∘ (lift γ')) H)) ⊆ H.
Proof.
  move => HSafety_H. move: (HSafe_SCH HSafety_H) => H_SSC.
  eapply (@hprop_subset_trans _
                              (lift τ' (sCl (lift γ' H)))
                              ((sCl ∘ (lift τ')) (sCl (lift γ' H)))
                              H). 
  by apply: sCl_bigger. 
  apply: Galois_fst_SSCH. by apply: γ'_upper_adjoint_τ'. assumption.   
Qed. 

(*CA:  by G2 we know ((lift τ') ((sCl ∘ (lift γ')) H)) ⊆ H and 
       by H ∈ HSafe we know that H ⊃ Cl _ *)
Lemma G2_HSafety (H: @hprop target) : HSafe H ->  ((hsCl ∘(lift τ')) ((sCl ∘ (lift γ')) H)) ⊆ H.
Admitted. 


(*CA: if we want to remove further assumptions 
      we have to look at all subset-closed hprop in the target! *)
Theorem tilde_RHSC_τRSSCHP:
   tilde_RHSC <-> (forall P (H: @hprop source), SSC H ->  τRhP (hsCl ∘ (lift τ')) P H).
Proof.
  split.
  - move => H_tilde P H H_ssc.
    rewrite /τRhP contra !neg_rhsat. move => [Ct H_tgt].
    have Cl_Hsafety : HSafe (hsCl (lift τ' H)) by apply: hsCl_HSafe. 
    destruct (Cl_Hsafety _ H_tgt) as [M [M_obs [M_leq_beh M_wit]]].
    destruct (H_tilde P Ct M) as [Cs H_src]; auto. 
    have not_τ_src_beh: ~ hsCl (lift τ' H) (τ' (beh (plug P Cs))).
    { apply: M_wit. by rewrite -conclusion_RSHC. }
    exists Cs => Hf. apply: not_τ_src_beh. 
    apply: hsCl_sCl. exists (τ' (beh (plug P Cs))).
    split; auto. by exists (beh (plug P Cs)).     
  - move => τRHSP P Ct M M_obs M_leq_tgt_beh.
    have SSC_H: SSC ((sCl ∘ (lift γ')) (fun b => ~ M <<< b)) by apply sCl_SCH. 
    have not_H_beh_tgt : ~ (hsCl ∘ (lift τ')) ((sCl ∘ (lift γ')) (fun b => ~ M <<< b))
                           (beh (plug (P↓) Ct)).
    { move => Hf. apply G2_HSafety in Hf. contradiction. 
        by apply: hsCl_HSafe. }
    move/contra : (τRHSP P (sCl (lift γ' (fun b : prop => ~ M <<< b))) SSC_H).
    rewrite !neg_rhsat => Hp.
    destruct Hp as [Cs H_src]; eauto.
    exists Cs. rewrite conclusion_RSHC. 
    apply: NNPP => Hf.
    apply: H_src.
    exists (γ' (τ' (beh (plug P Cs)))).
    split.
    + by exists (τ' (beh (plug P Cs))).
    + have H_adj : Adjunction_law γ' τ' by apply: γ'_upper_adjoint_τ'. 
      move/Galois_equiv : H_adj.
      move => [mono_gamma [mono_tau [G1 G2]]]. by apply: G1.
Qed.       
   
        
(* CA: notice that here we close (γ' H) only under subsets, 
       not in the class of the hypersafety
 *)
Theorem tilde_RHSC_γRHSP :
  tilde_RHSC <-> (forall P (H: @hprop target), HSafe H ->  σRhP (sCl ∘ (lift γ')) P H).
Proof.
  have H_adj : Adjunction_law γ' τ' by apply: γ'_upper_adjoint_τ'. 
  split.
  - move => H_tilde P H H_HSafe.
    rewrite /σRhP contra !neg_rhsat. move => [Ct H_tgt].
    destruct (H_HSafe _ H_tgt) as  [M [M_obs [M_leq_beh M_wit]]].
    destruct (H_tilde P Ct M) as [Cs H_conclusion]; auto.
    move/conclusion_RSHC : H_conclusion => H_conclusion.
    exists Cs => Hf. destruct Hf as [bs [H_bs beh_γ_bs]].
    destruct H_bs as [bt [H_bt Heq]]. subst.
    move/H_adj : beh_γ_bs => τ_beh_bt.
    apply: (M_wit bt); auto.  
    { move => m M_m. destruct (H_conclusion m) as [t [H_t pref_m_t]]; auto.
      exists t. split; auto. } 
  - move => Hγ P Ct M M_obs M_leq_beh_tgt.
    have HSafe_H : HSafe (fun b :@prop target => ~ M <<< b).
    { move => b. rewrite -dne => M_b. now exists M. }    
    move/contra: (Hγ P (fun b : prop => ~ M <<< b) HSafe_H).
    rewrite !neg_rhsat. move => HγP.
    destruct HγP as [Cs H_src]. by exists Ct. 
    exists Cs. rewrite conclusion_RSHC.
    apply: NNPP => Hf. apply: H_src.                                  
    exists (γ' (τ' (beh (plug P Cs)))). split.              
    + by exists (τ' (beh (plug P Cs))).
    +  move/Galois_equiv : H_adj.
       move => [mono_gamma [mono_tau [G1 G2]]]. by apply: G1. 
Qed.       