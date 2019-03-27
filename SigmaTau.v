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

Theorem tilde_RSCHC_τRSCHP :
  (total_rel rel) ->
  (Galois_snd σ' τ') ->
  tilde_RSCHC <-> (forall P (H: @hprop source), SSC H ->  τRhP (sCl ∘ (lift τ')) P H). 
Proof.
  move => Hrel G2. split. 
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
        in particular we need monotonicity *)
Theorem tilde_RSCHC_σRSCHP :
  Adjunction_law σ' τ' ->
  tilde_RSCHC <-> (forall P (H: @hprop target), SSC H ->  σRhP (sCl ∘ (lift σ')) P H).
Proof.
  move => H_adj. rewrite (τRSCHP_σRSCHP H_adj).
  move/Galois_equiv: H_adj => [mono_tau [mono_sigma [G1 G2]]].
  have h_rel : total_rel rel by apply: Galois_implies_total_rel. 
  by rewrite tilde_RSCHC_τRSCHP. 
Qed.

(******************************************************************************)
(** *HyperSafety *)
(******************************************************************************)

Definition tilde_RHSC := forall P Ct (M : finpref -> Prop),
                            Observations M ->
                            M <<< (beh (plug (P↓) Ct)) ->
                            (exists Cs, forall m, M m -> exists t s, prefix m t /\ 
                                                            rel s t /\
                                                    beh (plug P Cs) s).

Lemma tilde_RSCHC_tilde_RHSC : tilde_RSCHC -> tilde_RHSC.
Proof.
  move => H_tilde P Ct M Obs_M H_M.
  destruct (H_tilde P Ct) as [Cs H_Cs].
  exists Cs => m M_m.
  destruct (H_M m M_m) as [t [H_t m_pref_t]].  
  destruct (H_Cs t H_t) as [s [rel_s_t H_s]]. now exists t, s.
Qed. 

(* TODO: prove HSafety ⊆ SCH and get these from above *)
Lemma Galois_fst_HSafe  (σ : @prop target -> @prop source)
                        (τ : @prop source -> @prop target) :
  Adjunction_law σ τ ->
  (forall H : @hprop target, HSafe H -> (hsCl ∘ (lift τ)) ((hsCl ∘ (lift σ)) H) ⊆ H). 
Proof. Admitted.  
                                                 
Lemma Galois_snd_HSafe  (σ : @prop target -> @prop source)
                        (τ : @prop source -> @prop target) :
  Adjunction_law σ τ ->
  (forall H : @hprop source, HSafe H -> H ⊆ (hsCl ∘ (lift σ)) ((hsCl ∘ (lift τ)) H)).
Proof. Admitted.

Theorem tilde_RHSC_τRHSP :
  (Adjunction_law σ' τ') ->
  tilde_RHSC <-> (forall P (H: @hprop source), HSafe H ->  τRhP (hsCl ∘ (lift τ')) P H).
Proof.
  move => H_adj. 
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
    have σ_safe : HSafe ((hsCl ∘ (lift σ')) (fun b => ~ (M <<< b))) by apply: hsCl_HSafe. 
    move: (τ_pres P ( (hsCl ∘ (lift σ')) (fun b => ~ (M <<< b))) σ_safe).
    move/contra => HH. move: HH. rewrite !neg_rhsat => τ_pres_P.
    destruct τ_pres_P as [Cs src_beh].
    { exists Ct => H_false.
      move/Galois_fst_HSafe: H_adj => H_adj.
      have H_t_HSafe : HSafe (fun b => ~ M <<< b).
        { exists M. repeat (split; auto). by apply: NNPP. }   
          specialize (H_adj (fun b => ~ M <<< b) H_t_HSafe).
          move/dne : M_leq_beh_tgt => M_leq_beh_tgt. apply: M_leq_beh_tgt.
            by apply: H_adj.
    }
    have M_leq_τ_beh_src: M <<< (τ' (beh (plug P Cs))).
    { have src_subset : ~ sCl (lift σ' (fun b : prop => ~ M <<< b)) (beh (plug P Cs)).
      { move => Hfoo. by apply: (src_beh (hsCl_sCl Hfoo)). } 
      have  Hτ : ~ (sCl (fun b : prop => ~ M <<< b)) (τ' (beh (plug P Cs))).   
      { move => [bt [M_leq_bt H_bt]]. apply: src_subset.
        exists (σ' bt). split; [by exists bt | by rewrite -H_adj]. }
      apply: NNPP. move => Hf. apply: Hτ. by exists (τ' (beh (plug P Cs))). } 
    exists Cs => m M_m. destruct (M_leq_τ_beh_src m M_m) as [t [τt prefix_m_t]].
    move: τt. rewrite /τ'. move => [s [H_t rel_s_t]]. by exists t, s.    
Qed. 

Theorem tilde_RHSC_σRHSP :
  (Adjunction_law σ' τ') ->
  tilde_RHSC <-> (forall P (H: @hprop target), HSafe H ->  σRhP (hsCl ∘ (lift σ')) P H).
Proof.
  move => H_adj.
  split.
  - move => H_tilde P Ht Ht_HSafe. rewrite /σRhP contra !neg_rhsat.
    move => [Ct not_Ht_beh_tgt].
    destruct (Ht_HSafe _ not_Ht_beh_tgt) as [M [Obs_M [M_leq_beh_tgt bad_M]]]. 
    destruct (H_tilde P Ct M Obs_M) as [Cs H_src]; auto.
    exists Cs => σ_src.
    have τ_σ_beh_src: (hsCl (lift τ' (hsCl (lift σ' Ht)))) (τ' (beh (plug P Cs))).
    { apply: hsCl_bigger. by exists (beh (plug P Cs)). }
    have Ht_τ_beh_src: Ht (τ' (beh (plug  P Cs))).
    {  move/Galois_fst_HSafe: H_adj => H_use. 
         by apply: H_use. }
    have M_let_τ_beh_src: M <<< τ' (beh (plug P Cs)).
    { move => m M_m. move: (H_src m M_m). firstorder. }
      by apply: (bad_M (τ' (beh (plug P Cs)))).
  - admit.
Admitted.     