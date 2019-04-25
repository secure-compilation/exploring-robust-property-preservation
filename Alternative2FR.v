Require Import ClassicalExtras.
Require Import Setoid.
Require Import Events.
Require Import CommonST.
Require Import TraceModel.
Require Import Robustdef.
Require Import Properties.
Require Import Criteria.

(** Equivalent formulations for the robust preservation
    of 2-relational (hyper)properties classes
    in terms of pair of (hyper)properties of the corresponding class 
 *)

(** *Robust preservation of 2-relSafety  *)

Definition R2rSP_a := 
    forall P1 P2 S1 S2, 
    Safety S1 -> Safety S2 ->  
    (forall Cs, sat (Cs [P1]) S1 \/ sat (Cs[P2]) S2) -> 
    (forall Ct, sat (Ct [P1↓]) S1 \/ sat (Ct[P2↓]) S2).


Definition R2rSP_a_contra :
  R2rSP_a <->
  (forall P1 P2 S1 S2,
    Safety S1 -> Safety S2 ->
    (exists Ct, ~ sat (Ct [P1 ↓]) S1 /\ ~ sat (Ct [P2 ↓]) S2) ->
    (exists Cs, ~ sat (Cs [P1]) S1 /\ ~ sat (Cs [P2]) S2)).
Proof.
  split; intros Hr.
  + intros P1 P2 S1 S2 Hs1 Hs2. rewrite contra.
    repeat rewrite not_ex_forall_not.
    intros Has Ct [Hf1 Hf2]. 
    specialize (Hr P1 P2 S1 S2 Hs1 Hs2).
    assert (Hp:  (forall Cs : ctx src, sat (Cs [P1]) S1 \/ sat (Cs [P2]) S2)).
    { intros Cs. specialize (Has Cs). rewrite de_morgan1 in Has.
      repeat rewrite <- dne in Has. assumption. }
    destruct (Hr Hp Ct); contradiction.
  + intros P1 P2 S1 S2 Hs1 Hs2. rewrite  contra.
    repeat rewrite not_forall_ex_not.
    intros [Ct Hct]. rewrite de_morgan2 in Hct.
    destruct (Hr P1 P2 S1 S2 Hs1 Hs2) as [Cs H].
    now exists Ct. exists Cs. now rewrite de_morgan2.
Qed.   

Theorem alternative_R2rSP : R2rSP_a <-> R2rSP.
Proof.
  rewrite R2rSP_a_contra, <- R2rSC_R2rSP.
  split; intros H.
  + intros Ct P1 P2 m1 m2 H1 H2.
    specialize (H P1 P2 (fun t => ~ prefix m1 t) (fun t => ~ prefix m2 t)).
    assert (s1 : Safety  (fun t => ~ prefix m1 t)).
    { intros t Ht. apply NNPP in Ht. now exists m1. }  
    assert (s2 : Safety  (fun t => ~ prefix m2 t)).
    { intros t Ht. apply NNPP in Ht. now exists m2. } 
    specialize (H s1 s2). destruct H as [Cs [Hc1 Hc2]].
    exists Ct. split.
    ++ intros Hs.
       destruct (H1) as [t1 [Hpref Ht1]].
       specialize (Hs t1 Ht1). simpl in Hs. contradiction.   
    ++ intros Hs.
       destruct (H2) as [t2 [Hpref Ht2]].
       specialize (Hs t2 Ht2). simpl in Hs. contradiction.
    ++ exists Cs. split.
       +++ unfold sat in Hc1. rewrite not_forall_ex_not in Hc1.
           destruct Hc1 as [t1 Hc1].
           rewrite not_imp in Hc1. exists t1. 
           destruct Hc1 as [Hc11 Hc12].
           rewrite <- dne in Hc12. now auto. 
       +++ unfold sat in Hc2. rewrite not_forall_ex_not in Hc2.
           destruct Hc2 as [t2 Hc2].
           rewrite not_imp in Hc2. exists t2. 
           destruct Hc2 as [Hc21 Hc22].
           rewrite <- dne in Hc22. now auto.
  + intros P1 P2 S1 S2 HS1 HS2 [Ct [Hc1 Hc2]].
    unfold sat in Hc1,Hc2.
    rewrite not_forall_ex_not in Hc1,Hc2.
    destruct Hc1 as [t1 Hc1]. destruct Hc2 as [t2 Hc2].
    rewrite not_imp in Hc1,Hc2.
    destruct Hc1 as [Hc1 Ht1]. destruct Hc2 as [Hc2 Ht2].
    destruct (HS1 t1 Ht1) as [m1 [Hpref1 H1]].
    destruct (HS2 t2 Ht2) as [m2 [Hpref2 H2]].
    specialize (H Ct P1 P2 m1 m2). destruct H as [Cs [Hpsem1 Hpsem2]].
    ++ now exists t1.
    ++ now exists t2.
    ++ destruct Hpsem1 as [tt1 [Hm1 Hsem1]]. destruct Hpsem2 as [tt2 [Hm2 Hsem2]]. 
       exists Cs. split; unfold sat; rewrite not_forall_ex_not;
               [exists tt1 |exists tt2]; rewrite not_imp; now auto.                 
Qed.

(** *Robust preservation of relSafety  *)

Definition RrSP_a :=
 forall (I : Type), forall (ρ : I -> par src) (δ : I -> {π | Safety π}),
     (forall Cs, exists i, sat (Cs [(ρ i)]) (proj1_sig (δ i))) ->
     (forall Ct, exists j, sat (Ct [(ρ j) ↓]) (proj1_sig (δ j))).

Lemma RrSP_a_contra :
  RrSP_a <->
  ( forall (I : Type), forall (ρ : I -> par src) (δ : I -> {π | Safety π}),
     (exists Ct, forall i, ~ sat (Ct [(ρ i) ↓]) (proj1_sig (δ i))) -> 
     (exists Cs, forall i, ~ sat (Cs [(ρ i)]) (proj1_sig (δ i))) ). 
Proof.
  split; intros Hr.
  + intros I ρ δ. 
    specialize (Hr I ρ δ). rewrite contra.
    repeat rewrite not_ex_forall_not.
    intros H Ct.
    assert (HH: (forall Cs : ctx src, exists i : I, sat (Cs [ρ i]) (proj1_sig (δ i)))).
    { intros Cs. specialize (H Cs). rewrite not_forall_ex_not in H.
      destruct H as [i H]. rewrite <- dne in H. now exists i. }
    specialize (Hr HH Ct). destruct Hr as [i Hr].
    rewrite not_forall_ex_not. exists i. now rewrite <- dne.
  + intros I ρ δ. 
    specialize (Hr I ρ δ). rewrite contra.
    repeat rewrite not_forall_ex_not.
    intros [Ct H].
    assert (HH:  (exists Ct : ctx tgt, forall i : I, ~ sat (Ct [ρ i ↓]) (proj1_sig (δ i)))). 
    { exists Ct. now rewrite not_ex_forall_not in H. } 
    specialize (Hr HH). destruct Hr as [Cs Hr].
    exists Cs. now rewrite not_ex_forall_not.
Qed.


Theorem alternative_RrSP' : RrSP' <-> RrSP_a.
Proof.
  rewrite RrSP_a_contra, <- RrSC_RrSP'. 
  split; intro Hr.
  + intros I ρ δ [Ct Hct].
    specialize (Hr Ct  (fun P m => psem (Ct [P↓]) m) ). 
    destruct Hr as [Cs H]. 
    firstorder.
    exists Cs. intro i. specialize (Hct i). specialize (H (ρ i)). 
    unfold sat in *.
    rewrite not_forall_ex_not in *.  
    destruct Hct as [t Hct]. 
    rewrite not_imp in Hct.  destruct Hct as [Ht1 Ht2].
    destruct (proj2_sig (δ i) t) as [m [Hpref Hm]]; auto.
    destruct (H m) as [t' [Ht' HHt']].
    now exists t. exists t'.
    rewrite not_imp. firstorder.
  + intros Ct f H. 
    remember (fun (mP : finpref * (par src) | (f (snd mP) (fst mP))) => (snd (proj1_sig mP))) as ρ. 
    remember (fun m => (fun t => ~ prefix m t)) as δm. 
    assert (Hs_m : forall m, Safety (δm m)).
    { intros m t Ht. rewrite Heqδm in *. rewrite <- dne in Ht.
      now exists m.  }
    remember (fun (mP : finpref * (par src)| f (snd mP) (fst mP)) =>
                @exist prop Safety (δm (fst (proj1_sig mP)))
                                   (Hs_m (fst (proj1_sig mP)))) as δ. 
    specialize (Hr {mP | f (snd mP) (fst mP)} ρ δ).
    destruct Hr as [Cs Hr].
    exists Ct. intros [ (m,P) HH]. rewrite Heqδ, Heqρ. simpl in *. 
    rewrite Heqδm. unfold sat. rewrite not_forall_ex_not. 
    specialize (H P m HH). now firstorder.
    exists Cs. rewrite Heqδ, Heqρ in *. simpl in *.
    intros P m HPm.
    remember (fun x => f (snd x) (fst x)) as f_u.
    assert (Hu : f_u (m,P)). { rewrite Heqf_u. auto. }     
    specialize (Hr (@exist (finpref * (par src)) f_u (m,P) Hu )).
    simpl in *. unfold sat in Hr.
    rewrite not_forall_ex_not in Hr. destruct Hr as [t Hr].
    rewrite not_imp in Hr.
    rewrite Heqδm in Hr. rewrite <- dne in Hr.
    now exists t.
Qed.
    
(* CA: 
   What follows seems stronger than RrSP 

Definition RrSP_a' :=
  forall (Pf : par src -> Prop) (Sf : { π | Safety π} -> Prop),
    (forall Cs, exists P S, Pf P /\ Sf S /\ sat (Cs [P]) (proj1_sig S) ->
    (forall Ct, exists P' S', Pf P' /\ Sf S' /\ sat (Ct [P' ↓]) (proj1_sig S'))). 

Lemma RrSP_a'_contra :
  RrSP' <->
   forall (Pf : par src -> Prop) (Sf : { π | Safety π} -> Prop),
     (exists Ct, forall P' S', Pf P' -> Sf S' -> ~ sat (Ct [P' ↓]) (proj1_sig S')) ->
     (exists Cs, forall P S, Pf P -> Sf S -> ~ sat (Cs [P]) (proj1_sig S)).
Admitted. 
                  
*) 
                        
        
(** *Robust preservation of 2rel properties  *)


Definition R2rTP_a :=
  forall (P1 P2 : par src) (π1 π2 : prop),
    (forall Cs, sat (Cs[P1]) π1 \/ sat (Cs[P2]) π2) ->
    (forall Ct, sat (Ct[P1↓]) π1 \/  sat (Ct[P2↓]) π2). 

Lemma R2rTP_a_contra :
  R2rTP_a <->
   forall (P1 P2 : par src) (π1 π2 : prop),
    (exists Ct, ~ sat (Ct[P1↓]) π1 /\ ~ sat (Ct[P2↓]) π2) -> 
    (exists Cs, ~ sat (Cs[P1]) π1 /\ ~ sat (Cs[P2]) π2).
Proof.
  split; intros Hr.
  + intros P1 P2 π1 π2 [Ct H1].
    rewrite <- de_morgan2 in H1.
    specialize (Hr P1 P2 π1 π2). rewrite contra in Hr.
    repeat rewrite not_forall_ex_not in Hr.
    destruct Hr as [Cs Hr].
    now exists Ct. exists Cs. now rewrite <- de_morgan2. 
  + intros P1 P2 π1 π2. specialize (Hr P1 P2 π1 π2).
    rewrite contra. repeat rewrite not_forall_ex_not.
    intros [Ct Ht]. destruct Hr as [Cs Hr].
    exists Ct. now rewrite <- de_morgan2.
    exists Cs. now rewrite de_morgan2.
Qed.     
          
Theorem alternative_R2rTP : R2rTP <-> R2rTP_a.
Proof.
  rewrite <- R2rTC_R2rTP, R2rTP_a_contra.
  split; intros Hr.
  + intros P1 P2 π1 π2 [Ct [H1 H2]].
    unfold sat in H1, H2. 
    rewrite not_forall_ex_not in H1, H2.
    destruct H1 as [t1 H1]. destruct H2 as [t2 H2].
    rewrite not_imp in H1, H2.
    destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
    destruct (Hr Ct P1 P2 t1 t2) as [Cs [Hc1 Hc2]]; auto.
    exists Cs. split; unfold sat; rewrite not_forall_ex_not;
            [exists t1 | exists t2]; firstorder.
  + intros Ct P1 P2 t1 t2 Hsem1 Hsem2.   
    destruct (Hr P1 P2 (fun t => t <> t1) (fun t => t <> t2)) as [Cs [H1 H2]].
    { exists Ct. split; unfold sat; rewrite not_forall_ex_not;
              [exists t1 | exists t2]; rewrite not_imp; now rewrite <- dne. }
    exists Cs. unfold sat in H1, H2. rewrite not_forall_ex_not in H1, H2.
    destruct H1 as [tt1 H1]. destruct H2 as [tt2 H2].
    rewrite not_imp in H1, H2.
    destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
    rewrite <- dne in H12, H22. now subst.
Qed.


(** *Robust preservation of 2rel hyperproperties  *)

Definition R2rHP_a :=
  forall (P1 P2 : par src) (H1 H2 : hprop),
    (forall Cs, H1 (beh(Cs[P1])) \/ H2 (beh(Cs[P2]))) ->
    (forall Ct, H1 (beh(Ct[P1↓])) \/ H2 (beh(Ct[P2↓]))). 

Lemma R2rHP_a_contra :
  R2rHP_a <->
   forall (P1 P2 : par src) (H1 H2 : hprop),
     (exists Ct, ~ H1 (beh(Ct[P1↓])) /\ ~ H2 (beh(Ct[P2↓]))) ->
     (exists Cs, ~ H1 (beh(Cs[P1])) /\ ~ H2 (beh(Cs[P2]))).
Proof.
  split; intros Hr. 
  + intros P1 P2 H1 H2. rewrite contra.
    repeat rewrite not_ex_forall_not. 
    specialize (Hr P1 P2 H1 H2). intros HH.
    assert (K : (forall Cs : ctx src, H1 (beh (Cs [P1])) \/ H2 (beh (Cs [P2])))).
    { intros Cs. specialize (HH Cs). rewrite de_morgan1 in HH.
      repeat rewrite <- dne in HH. assumption. }
    specialize (Hr K). intros Ct. specialize (Hr Ct).
    rewrite de_morgan1. repeat rewrite <- dne. assumption.
  + intros P1 P2 H1 H2. rewrite contra. repeat rewrite not_forall_ex_not.
    specialize (Hr P1 P2 H1 H2).
    intros [Ct HH]. destruct Hr as [Cs KK].
    { exists Ct. now rewrite <- de_morgan2. }
    exists Cs. now rewrite de_morgan2. 
Qed.

Theorem alternative_R2rHP : R2rHP <-> R2rHP_a.
Proof.
  rewrite <- R2rHC_R2rHP, R2rHP_a_contra. 
  split; intros Hr.
  + intros P1 P2 H1 H2 [Ct [HH1 HH2]].
    destruct (Hr P1 P2 Ct) as [Cs [Heq1 Heq2]].
    assert (beh (Ct[P1↓]) = beh (Cs[P1])). 
    { unfold beh. now rewrite Heq1. }
    assert (beh (Ct[P2↓]) = beh (Cs[P2])). 
    { unfold beh. now rewrite Heq2. }
    exists Cs. now rewrite <- H, <- H0.
  +  intros P1 P2 Ct.
     specialize (Hr P1 P2 (fun π => π <> beh(Ct[P1↓])) (fun π => π <> beh(Ct[P2↓]))).
     destruct Hr as [Cs [HH1 HH2]].
     { exists Ct. repeat rewrite <- dne. auto. }
     rewrite <- dne in HH1, HH2.
     now exists Cs.
Qed.


(** *Robust preservation of rel hyperproperties  *)

Definition RrHP_a :=
  forall (I : Type), forall (ρ : I -> par src) (δ : I -> hprop),
     (forall Cs, exists i, (δ i) (beh (Cs [(ρ i)]))) ->
     (forall Ct, exists j, (δ j) (beh (Ct [(ρ j)↓]))).

Lemma RrHP_a_contra :
  RrHP_a <->
    forall (I : Type), forall (ρ : I -> par src) (δ : I -> hprop),
        (exists Ct, forall j, ~ (δ j) (beh (Ct [(ρ j)↓]))) ->
        (exists Cs, forall j, ~ (δ j) (beh (Cs [(ρ j)]))).
Proof.
  split; intros Hr.
  + intros I ρ δ. specialize (Hr I ρ δ).
    rewrite contra in Hr.
    repeat rewrite not_forall_ex_not in Hr.
    intros [Ct Ht]. destruct Hr as [Cs Hs].
    { exists Ct. now rewrite not_ex_forall_not. }
    exists Cs. now rewrite <- not_ex_forall_not.
  + intros I ρ δ. specialize (Hr I ρ δ).
    rewrite contra. 
    repeat rewrite not_forall_ex_not. 
    intros [Ct Ht]. destruct Hr as [Cs Hs].
    { exists Ct. now rewrite <- not_ex_forall_not. }
    exists Cs. now rewrite not_ex_forall_not.
Qed. 

Theorem alternative_RrHP' : RrHP' <-> RrHP_a.
Proof.
  rewrite <- RrHC_RrHP', RrHP_a_contra. 
  split; intro Hr.
  + intros I ρ δ [Ct Ht].
    destruct (Hr Ct) as [Cs Hs].
    assert (forall j, beh (Ct [ρ j ↓]) = beh (Cs [ρ j])).
    { intro j. specialize (Hs (ρ j)). now unfold beh. }
    exists Cs. intros j. now rewrite <- (H j).     
  + intros Ct.
    remember (fun P : (par src) => P) as ρ.  
    remember (fun P : (par src) => (fun π => π <> (beh (Ct [P ↓])))) as δ.  
    specialize (Hr (par src) ρ δ).
    destruct Hr as [Cs Hs].
    { exists Ct. intros k. rewrite Heqδ, Heqρ. tauto. }
    exists Cs. intros P. specialize (Hs P).
    rewrite Heqδ, Heqρ in Hs. rewrite <- dne in Hs.
    unfold beh in Hs. firstorder.
Qed. 
    
(* random remarks from previous notes 


   a 2-rel hyperproperty is an element of 2^(beh × beh) 

   if X is an infinite set, then X × X ≅ X (using AC). 

   This means that 2^(beh × beh) ≅ 2^beh × 2^beh. 

   The bijection above is, in general, non constructive.

*)    
