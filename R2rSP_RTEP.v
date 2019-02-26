Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.
Require Import List.
Require Import TechnicalLemmas.
Require Import Criteria. 

(** This file proves that R2rSC can imply RTEP *)

(* Definition two_rRSC : Prop := *)
(*   forall (r : finpref -> finpref -> Prop) P1 P2 , *)
(*     ((forall Cs m1 m2, psem (Cs [P1]) m1 -> *)
(*                   psem (Cs [P2]) m2 -> *)
(*                    r m1 m2) -> *)
(*      (forall Ct m1 m2, psem (Ct [P1 ↓]) m1 -> *)
(*                   psem (Ct [P2 ↓]) m2 -> *)
(*                   r m1 m2)). *)


(** *our assumptions *)
(**********************************************************)
Hypothesis input_totality_tgt : input_totality tgt.
Hypothesis determinacy_src    : determinacy src.
Hypothesis tgt_sem            : semantics_safety_like tgt.
Hypothesis no_divergence : forall P' t, sem tgt P' t -> ~ diverges t.
(**********************************************************)

Lemma three_continuations_tbd :
  forall l t, prefix (ftbd l) t ->
         ( (exists e, t = tstop l e) \/
                 (t = tsilent l) \/
            (exists e, prefix (ftbd (snoc l e)) t)).
Proof.
  intros l [] Hpref.
  + simpl in Hpref. apply list_proper_or_equal in Hpref. destruct Hpref.
    ++ subst. left. now exists e.
    ++ right. right. firstorder.  
  + simpl in Hpref. apply list_proper_or_equal in Hpref. destruct Hpref.
    ++ subst. right. now left.
    ++ right. right. firstorder. 
  + generalize dependent s. induction l.
    ++ right. right. destruct s. now exists e. 
    ++ intros [] Hpref. inversion Hpref. simpl.
       destruct (IHl s) as [ [ef FALSE] | [ FALSE | [e0 HH] ]]; try now inversion FALSE; auto.
       now simpl. right. right. exists e0; firstorder.  
Qed.

Definition myr ( m1 m2 : finpref) : Prop :=
  (fpr m1 m2) \/ (fpr m2 m1) \/
  (exists l i1 i2, is_input i1 /\
               is_input i2 /\
               i1 <> i2 /\
               fpr (ftbd (snoc l i1)) m1 /\
               fpr (ftbd (snoc l i2)) m2).

Lemma myr_symmetric : forall m1 m2, myr m1 m2 -> myr m2 m1.
Proof. firstorder. Qed. 

(* equivalent version of auXiliary_tstop.
   CA: one might think to show myXr m1 m2 -> myr m1 m2  
       and get a shorter proof. 
       Here we re-do the proof to have it independent from Xprefix.v 
*)
Lemma auxiliary_tstop :
  forall m2 l1 e1 t2, prefix m2 t2 ->
                  traces_match (tstop l1 e1) t2 -> myr (fstop l1 e1) m2.
Proof.
  intros m2 l1 e1 t2 prefix2 [Heq | [ll [i1 [i2 [I1 [I2 [Idiff [l_prefix1 l_prefix2]]]]]]]].
  + rewrite <- Heq in *. destruct (same_ext (fstop l1 e1) m2 (tstop l1 e1)); simpl; auto;
                          [now left |  right; now left].
  + destruct m2, t2; simpl in prefix2; simpl in l_prefix1, l_prefix2; try now auto.   
    ++ inversion prefix2; subst.  
       right. right. now exists ll, i1, i2.
    ++ destruct (list_list_same_ext l (snoc ll i2) l0); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.  
    ++ destruct (list_list_same_ext l (snoc ll i2) l0); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.
    ++ destruct (list_stream_same_ext l (snoc ll i2) s); auto.
       * destruct (list_proper_or_equal _ _ H) as [HH | [a HH]].        
         ** subst. right. right. now exists ll, i1, i2.
         ** apply list_pref_snoc_pref in HH.
            right. left. simpl. apply (list_list_prefix_trans l (snoc ll i1) l1);auto.
            apply (list_list_prefix_trans l ll _); auto. now apply snoc_longer. 
       * right. right. now exists ll, i1, i2.   
Qed. 

Lemma auxiliary_ftbd:
  forall l1 l2 t1 t2, prefix (ftbd l1) t1 -> prefix (ftbd l2) t2 ->
                  traces_match t1 t2 -> myr (ftbd l1) (ftbd l2).
Proof.
  intros l1 l2 t1 t2 pref1 pref2 [Heq | [ll [i1 [i2 [I1 [I2 [Idiff [l_prefix1 l_prefix2]]]]]]]].
  + subst. destruct (same_ext (ftbd l1) (ftbd l2) t2); auto; [now left | right; now left]. 
  + assert (H1: prefix (ftbd (snoc ll i1)) t1).
    { destruct t1; simpl in *; now auto. }
    assert (H2 : prefix (ftbd (snoc ll i2)) t2).
    { destruct t2; simpl in *; now auto. }
    destruct (same_ext (ftbd l1) (ftbd (snoc ll i1)) t1) as [l1_shorter | l1_longer]; auto. 
    ++ destruct (same_ext (ftbd l2) (ftbd (snoc ll i2)) t2) as [l2_shorter | l2_longer]; auto.
       destruct (list_proper_or_equal _ _ l1_shorter) as [l1_ll | [a1 l1_ll]]; subst.
       * destruct (list_proper_or_equal _ _ l2_shorter) as [l2_ll | [a2 l2_ll]]; subst. 
          ** right. right. now exists ll, i1, i2. 
          ** apply list_pref_snoc_pref in l2_ll. right. left. simpl.
             apply (list_list_prefix_trans l2 ll _); auto. now apply snoc_longer.  
       * apply list_pref_snoc_pref in l1_ll.
         destruct (list_proper_or_equal _ _ l2_shorter) as [l2_ll | [a2 l2_ll]]; subst. 
         **  left. simpl. apply (list_list_prefix_trans l1 ll _ ); auto. now apply snoc_longer.  
         ** apply list_pref_snoc_pref in l2_ll. destruct (list_list_same_ext l1 l2 ll); auto;
                                                  [now left | right; now left].  
       * destruct (list_proper_or_equal  _ _ l1_shorter); auto; subst. 
         ** right. right. now exists ll, i1, i2.  
         ** destruct H as [a H]. apply list_pref_snoc_pref in H. left.
            simpl. apply (list_list_prefix_trans l1 ll l2); auto.
            simpl in l2_longer. apply (list_list_prefix_trans ll (snoc ll i2) l2); auto.
            now apply snoc_longer.  
    ++ destruct (same_ext (ftbd l2) (ftbd (snoc ll i2)) t2) as [l2_shorter | l2_longer]; auto.
       * destruct (list_proper_or_equal _ _ l2_shorter) as [l2_ll | [a2 l2_ll]]; subst. 
          ** right. right. now exists ll, i1, i2. 
          ** apply list_pref_snoc_pref in l2_ll. right. left. simpl.
             apply (list_list_prefix_trans l2 ll _); auto.
             apply (list_list_prefix_trans ll (snoc ll i1) _); auto. now apply snoc_longer.
        * right. right. now exists ll, i1, i2.
Qed.   
    

Lemma auxiliary_lemma (t1 t2 : trace) :
  traces_match t1 t2 ->
  forall m1 m2, prefix m1 t1 -> prefix m2 t2 -> myr m1 m2.
Proof.
  intros [Heq | [ll [i1 [i2 [I1 [I2 [Idiff [l_prefix1 l_prefix2]]]]]]]] m1 m2 prefix1 prefix2. 
  - subst. unfold myr. destruct (same_ext m1 m2 t2) as [go_left | go_right_left]; auto. 
  - destruct m1, m2.
    ++ destruct t1, t2; inversion prefix1; inversion prefix2; subst.
       right. right. now exists ll, i1, i2.
    ++ destruct t1; inversion prefix1; subst.  
       apply (auxiliary_tstop (ftbd l0) l1 e t2); auto.
       right. now exists ll, i1, i2. 
    ++ destruct t2; inversion prefix2; subst. apply myr_symmetric. 
       apply (auxiliary_tstop (ftbd l) l1 e t1); auto.
       right. exists ll, i2, i1. repeat (split; try now auto). 
    ++ apply (auxiliary_ftbd l l0 t1 t2); auto. right. now exists ll, i1, i2.  
Qed. 
  
Lemma teq_premises_myXr_holds : forall P1 P2,
    (forall Cs t, sem src (Cs [P1]) t <-> sem src (Cs [P2]) t) ->
    (forall Cs m1 m2, psem (Cs [P1]) m1 -> psem (Cs [P2]) m2 ->
                 myr m1 m2).
Proof.
  intros P1 P2 H Cs m1 m2 [t1 [pref1 sem1]] [t2 [pref2 sem2]].
    rewrite (H Cs t1) in sem1.
   specialize (determinacy_src (Cs[P2]) t1 t2 sem1 sem2). 
   intros Hmatch. now apply (auxiliary_lemma t1 t2).
Qed.
    

Lemma input_tot_consequence (W : prg tgt): forall l i1 i2,
    is_input i1 -> is_input i2 -> 
    psem W (ftbd (snoc l i1)) -> psem W (ftbd (snoc l i2)).
Proof.
  intros l i1 i2 Hi1 Hi2 [t [pref_x_t Hsemt]].
  assert (psem W (ftbd  (snoc l i1))).
  { simpl in *. now exists t. }
  now apply (input_totality_tgt W l i1 i2) in H.
Qed.  
 
Lemma t_being_tstop_leads_to_contra (W1 W2 : prg tgt) t l2 e2 
                                    (sem1 : sem tgt W1 t) (sem2 : sem tgt W2 (tstop l2 e2))
                                    (nsem12: ~ sem tgt W2 t)
                                    (xpref_x_t : prefix (ftbd l2) t)
  : 
    (forall m1 m2, psem W1 m1 -> psem W2 m2 -> myr m1 m2) -> False.
Proof.
 intros twoX. destruct t.
 - simpl in *. destruct (twoX (fstop l e) (fstop l2 e2))
     as [xpr1 | [xpr2 | [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]]]].
   now exists (tstop l e). now exists (tstop l2 e2).
   + inversion xpr1; subst. contradiction.
   + inversion xpr2; subst. contradiction.                                
   + simpl in Hxpr1, Hxpr2.
     apply (list_list_prefix_trans (snoc xx i2) l2 l Hxpr2) in xpref_x_t.   
     destruct (list_list_same_ext (snoc xx i1) (snoc xx i2) l) as [F | F]; auto;
       apply Hdiff; apply (list_snoc_diff xx _ _ ) in F; congruence.
 - now apply (no_divergence W1 (tsilent l)).  
 - simpl in xpref_x_t.
   destruct (tgt_sem (tstream s) W2 nsem12) as [l [ebad [Hpsem [Hpref Hnpsem]]]]; auto. 
   simpl in Hpref.
   destruct (twoX (ftbd (snoc l ebad)) (fstop l2 e2))
     as [xpr1 | [xpr2 | [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]]]]; auto.  
   now exists (tstream s). now exists (tstop l2 e2).
   + simpl in xpr1. apply Hnpsem. now exists (tstop l2 e2).
   + simpl in *.
     apply (list_stream_prefix_trans _ _ s) in Hxpr1; auto.  
     apply (list_stream_prefix_trans _ _ s) in Hxpr2; auto.  
     destruct (list_stream_same_ext (snoc xx i1) (snoc xx i2) s) as [F | F]; auto;
     apply Hdiff; apply (list_snoc_diff xx _ _) in F; congruence.         
Qed. 
 

Lemma violates_xmax  (W1 W2 : prg tgt) t t2 l a aa
                     (sem1 : sem tgt W1 t) (sem2 : sem tgt W2 t2)
                     (nsem12: ~ sem tgt W2 t)
                     (xpref_x_t : prefix (ftbd (snoc l aa)) t)
                     (x_t2 : prefix (ftbd (snoc l a)) t2)
                       
  :
    (forall m' : finpref, prefix m' t -> psem W2 m' -> fpr m' (ftbd l)) -> 
    (forall m1 m2, psem W1 m1 -> psem W2 m2 ->  myr m1 m2) -> False.
Proof.
  intros xmax twoX.
  assert (xsem1 : psem W1 (ftbd (snoc l aa))) by now exists t.
  assert (xsem2 : psem W2 (ftbd (snoc l a))) by now exists t2.
  specialize (twoX (ftbd (snoc l aa)) (ftbd (snoc l a)) xsem1 xsem2).
  destruct twoX as [xpr1 | [xpr2 | matching]].
  + simpl in xpr1. apply list_snoc_diff in xpr1. subst.
    specialize (xmax (ftbd (snoc l a)) xpref_x_t xsem2).
    simpl in xmax. now apply snoc_strictly_longer in xmax. 
  + simpl in xpr2. apply list_snoc_diff in xpr2. subst.
    specialize (xmax (ftbd (snoc l aa)) xpref_x_t xsem2).
    simpl in xmax. now apply snoc_strictly_longer in xmax. 
  + destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff_is [Hxpr1 Hxpr2 ]]]]]]].
    simpl in Hxpr1, Hxpr2.  
    apply (list_snoc_pointwise xx l i1 i2 aa a) in Hxpr2; auto.  
    destruct Hxpr2 as [H1 H2]. subst.
    apply (input_tot_consequence W2 l a aa) in xsem2; auto. 
    specialize (xmax (ftbd (snoc l aa)) xpref_x_t xsem2).
    simpl in xmax. now apply snoc_strictly_longer in xmax. 
Qed. 

Theorem R2rSP_RTEP : R2rSP -> RTEP.
Proof.
  rewrite <- R2rSC_R2rSP. rewrite R2rSC_R2rSC'.
  unfold R2rSC', RTEP.
  intros twoX P1 P2 Hsrc Ct t.
  specialize (twoX P1 P2 myr (teq_premises_myXr_holds P1 P2 Hsrc) Ct).
  split. 
  + intros case1.
    apply NNPP. intros t_not_sem2.
    destruct (longest_in_psem tgt_sem (Ct [P2↓]) t t_not_sem2) as [x [xpref_x_t [xsem2_x x_max]]].
    destruct xsem2_x as [t2 [x_t2 t2_sem2]].
    destruct x.
    ++ (* it can only be t2 '=' fstop p e = t *)
       destruct t, t2; auto.
       inversion xpref_x_t; inversion x_t2; subst; congruence.  
    ++ destruct (three_continuations_tbd l t2 x_t2) as [t2stop | [t2silent | t2longer]].
       +++ destruct t2stop as [e2 Ht2]. rewrite Ht2 in *. 
           now apply (t_being_tstop_leads_to_contra (Ct [P1↓]) (Ct [P2↓]) t l e2).
       +++ rewrite t2silent in *. 
           now apply (no_divergence (Ct [P2↓]) (tsilent l)).         
       +++ destruct t2longer as [a t2longer].
           destruct (three_continuations_tbd l t xpref_x_t) as [ttstop | [ttsilent | ttlonger]].           - destruct ttstop as [e ttstop]. subst. 
             destruct (twoX (fstop l e) (ftbd (snoc l a))) as [xpr1 | [xpr2 | matching]]; auto.
             now exists (tstop l e). now exists t2. 
             -- simpl in xpr2. now apply snoc_strictly_longer in xpr2. 
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2 ]]]]]]].
                simpl in Hxpr1, Hxpr2. 
                apply (snocs_aux_lemma xx l i2 i1 a); congruence.       
           - subst. now apply (no_divergence (Ct [P1↓]) (tsilent l)).
           - destruct ttlonger as [aa ttlonger].
             now apply (violates_xmax (Ct [P1↓]) (Ct [P2↓]) t t2 l a aa).              
  + intros case2.
    apply NNPP. intros t_not_sem1.
    destruct (longest_in_psem tgt_sem (Ct [P1↓]) t t_not_sem1) as [x [xpref_x_t [xsem1_x x_max]]].
    destruct xsem1_x as [t1 [x_t1 t1_sem1]].
    assert (twoX' : forall m1 m2, psem (Ct [P2 ↓]) m1 -> psem (Ct [P1 ↓]) m2 -> myr m1 m2).
    { intros x1 x2 H H0. apply myr_symmetric. now apply twoX. } 
    destruct x.
    ++ (* it can only be t2 '=' fstop p e = t *)
       destruct t, t1; auto.
       inversion xpref_x_t; inversion x_t1; subst; congruence.  
    ++ destruct (three_continuations_tbd l t1 x_t1) as [t1stop | [t1silent | t1longer]].
       +++ destruct t1stop as [e1 Ht1]. rewrite Ht1 in *. 
           now apply (t_being_tstop_leads_to_contra (Ct [P2↓]) (Ct [P1↓]) t l e1).
       +++ rewrite t1silent in *. 
           now apply (no_divergence (Ct [P1↓]) (tsilent l)).         
       +++ destruct t1longer as [a t1longer].
           destruct (three_continuations_tbd l t xpref_x_t) as [ttstop | [ttsilent | ttlonger]].
           - destruct ttstop as [e ttstop]. subst. 
             destruct (twoX' (fstop l e) (ftbd (snoc l a))) as [xpr1 | [xpr2 | matching]]; auto.
             now exists (tstop l e). now exists t1. 
             -- simpl in xpr2. now apply snoc_strictly_longer in xpr2. 
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2 ]]]]]]].
                simpl in Hxpr1, Hxpr2. 
                apply (snocs_aux_lemma xx l i2 i1 a); congruence.       
           - subst. now apply (no_divergence (Ct [P2↓]) (tsilent l)).
           - destruct ttlonger as [aa ttlonger].
             now apply (violates_xmax (Ct [P2↓]) (Ct [P1↓]) t t1 l a aa). 
Qed.    