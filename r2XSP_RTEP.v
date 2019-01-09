Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.
Require Import List.

Require Import XPrefix.
Require Import Criteria.

(** *our assumptions *)
(**********************************************************)
Hypothesis input_totality_tgt : input_totality tgt.
Hypothesis determinacy_src    : determinacy src.
Hypothesis tgt_sem           : semantics_safety_like tgt.
(**********************************************************)

(* CA: before trying to prove a lemma check if it is actually used or not! *)

(* Definition xsnoc (m : xpref) (e : event) := *)
(*   match m with *)
(*   | xstop _ _ | xsilent _ => m *)
(*   | xtbd  l               => xtbd (snoc l e) *)
(*   end.  *)


Fixpoint list_pref { A : Type } (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | nil, _ => True
  | cons x xs, cons y ys => x = y /\ list_pref xs ys
  | _, _ => False
  end.

Definition xpr (x1 x2 : xpref) : Prop :=
  match x1 with
  | xstop m1 s1 => match x2 with
                  | xstop m2 s2 => m1 = m2 /\ s1 = s2
                  | _ => False
                  end
                    
  | xsilent m1 => match x2 with
                 | xsilent m2 => m1 = m2
                 | _ => False
                 end
                   
  | xtbd m1 => match x2 with
              | xstop m2 s1 => list_pref m1 m2
              | xsilent m2  => list_pref m1 m2
              | xtbd m2 =>  list_pref m1 m2
              end
                
  end.

Definition xstopped x : bool :=
  match x with
  | xstop _ _ => true
  | _ => false
  end.

Lemma xpr_snoc : forall p a1 a2, 
    xpr (xtbd (snoc p a1)) (xtbd (snoc p a2)) -> a1 = a2.
Proof.
  induction p; intros a1 a2 H; simpl in *; destruct H as [H1 H2]; auto.   
Qed.

Fixpoint list_to_stop_trace (l : list event) (e : endstate) : trace :=
  match l with
  | nil => tstop e
  | cons l ls => tcons l (list_to_stop_trace ls e)
  end. 

Lemma xstop_prefix_list : forall p e, xprefix (xstop p e) (list_to_stop_trace p e).
Proof.
  induction p; intros e; simpl; auto.  
  split; auto. now apply IHp.
Qed.

Lemma unique_continuation_stop: forall l e t, xprefix (xstop l e) t -> t = list_to_stop_trace l e. 
Proof.
  intros l e. induction l.
  + intros [] Hxpref; auto; inversion Hxpref; now subst. 
  + intros [] Hxpref; inversion Hxpref. subst. 
    simpl. now rewrite (IHl t).    
Qed.

Fixpoint list_to_silent_trace (l : list event) : trace :=
  match l with
  | nil => tsilent
  | cons l ls => tcons l (list_to_silent_trace ls)
  end.

Lemma xsilent_prefix_list : forall p, xprefix (xsilent p) (list_to_silent_trace p).
Proof.
  induction p; simpl; auto.  
Qed.

Lemma unique_continuation_silent : forall l t, xprefix (xsilent l) t -> t = list_to_silent_trace l.
Proof.  
   intros l. induction l; intros [] Hxpref; auto; inversion Hxpref; subst. 
   simpl. now rewrite (IHl t).    
Qed. 
  
Lemma three_continuations_tbd :
  forall l t, xprefix (xtbd l) t ->
         ( (exists e, t = list_to_stop_trace l e) \/                                     
                 (t = list_to_silent_trace l) \/
            (exists e, xprefix (xtbd (snoc l e)) t)). 
Proof.
  intros l. induction l.
  + intros [] Hxpref.
    ++ left. now exists e.
    ++ right. now left.
    ++ right. right. now exists e.
  + intros [] Hxpref; inversion Hxpref; subst.
    destruct  (IHl t) as [K1 | [K2 | K3]]; auto.  
    ++ left. destruct K1 as [e0 K1]. exists e0. simpl. now rewrite K1.
    ++ right. left. simpl. now rewrite K2.
    ++ right. right. destruct K3 as [e0 K3]. now exists e0.
Qed.

Lemma xpr_longer_stop_contra : forall p a e, xpr (xtbd (snoc p a)) (xstop p e) -> False.
Proof.
  induction p; auto.
  simpl. intros a0 e [Hfoo H]. now apply (IHp a0 e). 
Qed.

Lemma xpr_longer_silent_contra : forall p a, xpr (xtbd (snoc p a)) (xsilent p) -> False.
Proof.
  induction p; auto.
  simpl. intros a0 [Hfoo H]. now apply (IHp a0).
Qed. 

Lemma xpr_longer_xtbd_contra: forall p a, xpr (xtbd (snoc p a)) (xtbd p) -> False.
Proof.
  induction p; auto.
  simpl. intros a0 [Hfoo H]. now apply (IHp a0).
Qed. 

Lemma list_snoc_pointwise: forall (l p : list event) i1 i2 a1 a2,
                          i1 <> i2 ->
                          list_pref (snoc l i1) (snoc p a1) ->
                          list_pref (snoc l i2) (snoc p a2) ->
                          (i1 = a1 /\ i2 = a2).
Admitted.

Lemma no_silent_and_stop: forall l1 l2 e,
    list_to_silent_trace l1 <> list_to_stop_trace l2 e.
Admitted. 

Lemma same_x_ext : forall x1 x2 t, xprefix x1 t -> xprefix x2 t -> xpr x1 x2 \/ xpr x2 x1. 
Proof.
  intros []; induction p; intros x2 t H1 H2. 
  + apply unique_continuation_stop in H1. subst.
    destruct x2.
    ++ destruct p. simpl in H2. subst. now left.
       simpl in *. contradiction.
    ++ destruct p. simpl in H2. subst. now right.
       simpl in *. contradiction.
    ++ destruct p. simpl in H2. contradiction.
       simpl in *. contradiction.
  + destruct t; simpl in H1; try contradiction. 
    inversion H1. subst.
    destruct x2.
    ++ destruct p0; simpl in H2. contradiction.
       inversion H2. subst.
       destruct (IHp (xstop p0 e1) t) as [K1 | K2]; auto. 
       +++ left. subst. simpl in *. firstorder. now rewrite H.
       +++ right. simpl in *. firstorder. now rewrite H.
    ++ destruct p0; simpl in H2. now right. 
       destruct (IHp (xtbd p0) t) as [K1 | K2]; auto. 
       +++ simpl. now destruct H2.  
       +++ right. simpl. firstorder.
    ++ apply unique_continuation_silent in H2. 
       apply unique_continuation_stop in H0.
       destruct p0; inversion H2.  
       rewrite H0 in H4. exfalso. symmetry in H4.
       now apply no_silent_and_stop in H4.     
  + left. now case x2.
  + admit.
Admitted.   
       
(*********************************************************************************)

Definition myXr (x1 x2: xpref) : Prop :=
  (xpr x1 x2) \/ (xpr x2 x1) \/
  (exists p i1 i2, is_input i1 /\
               is_input i2 /\
               i1 <> i2 /\
               xpr (xtbd (snoc p i1)) x1 /\
               xpr (xtbd (snoc p i2)) x2).


Lemma teq_premises_myXr_holds : forall P1 P2,
    (forall Cs t, sem src (Cs [P1]) t <-> sem src (Cs [P2]) t) ->
    (forall Cs x1 x2, xsem (Cs [P1]) x1 -> xsem (Cs [P2]) x2 ->
                 myXr x1 x2).
Proof.
  intros P1 P2 H Cs x1 x2 [t1 [xpref1 sem1]] [t2 [xpref2 sem2]].
  rewrite (H Cs t1) in sem1.
  destruct (determinacy_src (Cs[P2]) t1 t2 sem1 sem2) as [t_eq | matching].
  + rewrite t_eq in *.
    destruct (same_x_ext x1 x2 t2 xpref1 xpref2) as  [go_left | go_right];
      [now left | right; now left].
  + destruct matching as [m [i1 [i2 [I1 [I2 [Idiff [m_stop [m_prefix1 m_prefix2]]]]]]]].
    destruct m.
    ++ inversion m_stop.
    ++ simpl in m_prefix1, m_prefix2.
       destruct x1, x2.
       - apply unique_continuation_stop in xpref1.
         apply unique_continuation_stop in xpref2.
         rewrite xpref1 in m_prefix1. rewrite xpref2 in m_prefix2.
         right. right.
         exists p, i1, i2. repeat (split; try now auto);
         simpl in *. (* mprefix1 -> thesis, maybe a lemma is needed *) admit.
         (* mprefix2 -> thesis, maybe a lemma is needed *) admit.
       -  apply unique_continuation_stop in xpref1.
          rewrite xpref1 in m_prefix1.  
          (* p1 and (p; i2)  are comparable as both have t2 as extension, 
             if p1 ≤ p then by m_prefix1, p1 ≤ (xstop p0 e) and go in the first 2 disjuncts 
             if p1 = p;i2  then go right-right  
             if p1 > p;i2 then go right-right
           *) admit.
       - apply unique_continuation_stop in xpref1.
         apply unique_continuation_silent in xpref2.
         rewrite xpref1 in m_prefix1. rewrite xpref2 in m_prefix2.
         right. right.
         exists p, i1, i2. repeat (split; try now auto);
         simpl in *. (* mprefix1 -> thesis, maybe a lemma is needed *) admit.
         (* mprefix2 -> thesis, maybe a lemma is needed *) admit.
       -  apply unique_continuation_stop in xpref2.
          rewrite xpref2 in m_prefix2.
          (* p0 and (p; i1)  are comparable as both have t1 as extension, 
             if p0 ≤ p then by m_prefix2, p0 ≤ (xstop p1 e) and go in the first 2 disjuncts 
             if p0 = p;i1  then go right-right  
             if p0 > p;i1 then go right-right
           *) admit.
       - (* p0 and p1 are comparable with (snoc p i1) and (snoc p i2) respectively 
            from that deduce they are in myXr
          *) admit.
       - apply unique_continuation_silent in xpref2.
         rewrite xpref2 in m_prefix2.
         (* p0 and (p; i1) are comparable as both have t1 as extension 
            if p0 ≤ p then by m_prefix2, p0 ≤ (xsilent p1) and go in the first 2 disjuncts 
            if p0 = p;i1  then go right-right  
            if p0 > p;i1 then go right-right
          *) admit.
       - apply unique_continuation_silent in xpref1.
         apply unique_continuation_stop in xpref2.
         rewrite xpref1 in m_prefix1. rewrite xpref2 in m_prefix2.
         right. right.
         exists p, i1, i2. repeat (split; try now auto);
         simpl in *. (* mprefix1 -> thesis, maybe a lemma is needed *) admit.
         (* mprefix2 -> thesis, maybe a lemma is needed *) admit.
       - apply unique_continuation_silent in xpref1.
          rewrite xpref1 in m_prefix1.  
          (* p1 and (p; i2)  are comparable as both have t2 as extension, 
             if p1 ≤ p then by m_prefix1, p1 ≤ (xsilent p0) and go in the first 2 disjuncts 
             if p1 = p;i2  then go right-right  
             if p1 > p;i2 then go right-right
           *) admit.
       - apply unique_continuation_silent in xpref1.
         apply unique_continuation_silent in xpref2.
         rewrite xpref1 in m_prefix1. rewrite xpref2 in m_prefix2.
         right. right.
         exists p, i1, i2. repeat (split; try now auto);
         simpl in *. (* mprefix1 -> thesis, maybe a lemma is needed *) admit.
         (* mprefix2 -> thesis, maybe a lemma is needed *) admit.        
Admitted.


(* CA: painful but resonable, 
       if t = m;stop and we can use an argument similar to longest_in_psem 
       if t = m;silent ' '        ''         ''           ''         ''
       if t is infinite then we have to use semantics_safety_like and then 
       embed the given prefix 
 *)
Lemma  longest_in_xsem :
  forall W t, ~ sem tgt W t ->
    exists x, xprefix x t /\ xsem W x /\
     (forall x', xprefix x' t -> xsem W x' -> xpr x' x).
Admitted.



Definition  two_rRXC : Prop :=
  forall (r : xpref -> xpref -> Prop) P1 P2 ,
    ((forall Cs x1 x2, xsem (Cs [P1]) x1 ->
                  xsem (Cs [P2]) x2 ->
                   r x1 x2) ->
     (forall Ct x1 x2, xsem (Ct [P1 ↓]) x1 ->
                  xsem (Ct [P2 ↓]) x2 ->
                  r x1 x2)).

Lemma R2rXP_two : R2rXP <->  two_rRXC.
Admitted. 


Lemma input_tot_consequence (W : prg tgt): forall p i1 i2,
    is_input i1 -> is_input i2 -> 
    xsem W (xtbd (snoc p i1)) -> xsem W (xtbd (snoc p i2)).
Proof.
  intros p i1 i2 Hi1 Hi2 [t [xpref_x_t Hsemt]].
  assert (psem W (fsnoc (ftbd p) i1)).
  { simpl in *. now exists t. }
  now apply (input_totality_tgt W (ftbd p) i1 i2) in H.
Qed.  

Lemma t_being_tstop_leads_to_contra (W1 W2 : prg tgt) t t2 p
                                    (t2stop: exists e, t2 = list_to_stop_trace p e) 
                                    (sem1 : sem tgt W1 t) (sem2 : sem tgt W2 t2)
                                    (nsem12: ~ sem tgt W2 t) 
                                    (xpref_x_t : xprefix (xtbd p) t)
                                    (x_t2 : xprefix (xtbd p) t2)
  :
  (forall x1 x2, xsem W1 x1 -> xsem W2 x2 -> myXr x1 x2) -> False. 
Proof.
  intros twoX. 
 destruct (three_continuations_tbd p t xpref_x_t) as [ttstop | [ttsilent | ttlonger]].
           - destruct t2stop as [e2 t2stop]. destruct ttstop as [e ttstop].
             assert (xsem1 : xsem W1 (xstop p e)).
             { exists t. split; auto.
               rewrite ttstop. now apply xstop_prefix_list. }
             assert (xsem2 : xsem W2 (xstop p e2)).
             { exists t2. split; auto.
               rewrite t2stop. now apply xstop_prefix_list. }
             specialize (twoX (xstop p e) (xstop p e2) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- inversion xpr1. now subst.
             -- inversion xpr2. now subst.
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]].
                simpl in Hxpr1, Hxpr2. admit. (* contradiction! from Hxpr1, Hxpr2 we get i1 = i2 *)
           -  destruct t2stop as [e t2stop].
               assert (xsem1 : xsem W1 (xsilent p)).
             { exists t. split; auto.
               rewrite ttsilent. now apply xsilent_prefix_list. }
             assert (xsem2 : xsem W2 (xstop p e)).
             { exists t2. split; auto.
               rewrite t2stop. now apply xstop_prefix_list. }
             specialize (twoX (xsilent p) (xstop p e) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- inversion xpr1.
             -- inversion xpr2.
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]].
                 simpl in Hxpr1, Hxpr2. admit.  (* contradiction! from Hxpr1, Hxpr2 we get i1 = i2 *)
           - destruct t2stop as [e2 t2stop]. destruct ttlonger as [a ttstop].
             assert (xsem1 : xsem W1 (xtbd (snoc p a))) by now exists t.
             assert (xsem2 : xsem W2 (xstop p e2)).
             { exists t2. split; auto.
               rewrite t2stop. now apply xstop_prefix_list. }
             specialize (twoX (xtbd (snoc p a)) (xstop p e2) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- now apply xpr_longer_stop_contra in xpr1.
             -- inversion xpr2.
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]].
                 simpl in Hxpr1, Hxpr2. admit. (* contradiction from Hxpr1 and Hxpr2 *)
Admitted. 

Lemma t_being_tsilent_leads_to_contra (W1 W2 : prg tgt) t t2 p
                                      (t2silent: t2 = list_to_silent_trace p) 
                                      (sem1 : sem tgt W1 t) (sem2 : sem tgt W2 t2)
                                      (nsem12: ~ sem tgt W2 t) 
                                      (xpref_x_t : xprefix (xtbd p) t)
                                      (x_t2 : xprefix (xtbd p) t2)
  :
  (forall x1 x2, xsem W1 x1 -> xsem W2 x2 -> myXr x1 x2) -> False. 
Proof.
  intros twoX. 
 destruct (three_continuations_tbd p t xpref_x_t) as [ttstop | [ttsilent | ttlonger]].
           - destruct ttstop as [e ttstop].
             assert (xsem1 : xsem W1 (xstop p e)).
             { exists t. split; auto.
               rewrite ttstop. now apply xstop_prefix_list. }
             assert (xsem2 : xsem W2 (xsilent p)).
             { exists t2. split; auto.
               rewrite t2silent. now apply xsilent_prefix_list. }
             specialize (twoX (xstop p e) (xsilent p) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- inversion xpr1. 
             -- inversion xpr2. 
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]].
                simpl in Hxpr1, Hxpr2. admit. (* contradiction! from Hxpr1, Hxpr2 we get i1 = i2 *)
           - rewrite <- t2silent in ttsilent. now subst. 
           - destruct ttlonger as [a ttstop].
             assert (xsem1 : xsem W1 (xtbd (snoc p a))) by now exists t.
             assert (xsem2 : xsem W2 (xsilent p)).
             { exists t2. split; auto.
               rewrite t2silent. now apply xsilent_prefix_list. }
             specialize (twoX (xtbd (snoc p a)) (xsilent p) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- now apply xpr_longer_silent_contra in xpr1.
             -- inversion xpr2.
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2]]]]]]].
                simpl in Hxpr1, Hxpr2.  admit. (* contradiction from Hxpr1 and Hxpr2 *)
Admitted. 


Lemma violates_xmax  (W1 W2 : prg tgt) t t2 p a aa
                     (sem1 : sem tgt W1 t) (sem2 : sem tgt W2 t2)
                     (nsem12: ~ sem tgt W2 t)
                     (xpref_x_t : xprefix (xtbd (snoc p aa)) t)
                     (x_t2 : xprefix (xtbd (snoc p a)) t2)
                       
  :
    (forall x' : xpref, xprefix x' t -> xsem W2 x' -> xpr x' (xtbd p)) -> 
    (forall x1 x2, xsem W1 x1 -> xsem W2 x2 ->  myXr x1 x2) -> False.
Proof.
  intros xmax twoX.
  assert (xsem1 : xsem W1 (xtbd (snoc p aa))) by now exists t.
  assert (xsem2 : xsem W2 (xtbd (snoc p a))) by now exists t2.
  specialize (twoX (xtbd (snoc p aa)) (xtbd (snoc p a)) xsem1 xsem2).
  destruct twoX as [xpr1 | [xpr2 | matching]].
  + apply xpr_snoc in xpr1. subst.
    specialize (xmax (xtbd (snoc p a)) xpref_x_t xsem2).
    now apply xpr_longer_xtbd_contra in xmax.
  + apply xpr_snoc in xpr2. subst.
    specialize (xmax (xtbd (snoc p aa)) xpref_x_t xsem2).
    now apply xpr_longer_xtbd_contra in xmax.
  + destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff_is [Hxpr1 Hxpr2 ]]]]]]].
    simpl in Hxpr1, Hxpr2.  
    apply (list_snoc_pointwise xx p i1 i2 aa a) in Hxpr2; auto.  
    destruct Hxpr2 as [H1 H2]. subst.
    apply (input_tot_consequence W2 p a aa) in xsem2; auto. 
    specialize (xmax (xtbd (snoc p aa)) xpref_x_t xsem2).
    now apply xpr_longer_xtbd_contra in xmax. 
Qed. 
    

Theorem R2rXP_RTEP : R2rXP -> teq_preservation.
Proof.  
  rewrite R2rXP_two. unfold two_rRXC, teq_preservation.
  intros twoX P1 P2 Hsrc Ct t.
  specialize (twoX myXr P1 P2 (teq_premises_myXr_holds P1 P2 Hsrc) Ct).
  split.
  + intros case1.
    apply NNPP. intros t_not_sem2.
    destruct (longest_in_xsem (Ct [P2↓]) t t_not_sem2) as [x [xpref_x_t [xsem2_x x_max]]].
    destruct xsem2_x as [t2 [x_t2 t2_sem2]].
    destruct x.
    ++ (* it can only be t2 '=' xstop p e = t *)
       apply (unique_continuation_stop p e t) in xpref_x_t.
       apply (unique_continuation_stop p e t2) in x_t2.
       congruence.
    ++ destruct (three_continuations_tbd p t2 x_t2) as [t2stop | [t2silent | t2longer]].
       +++ now apply (t_being_tstop_leads_to_contra (Ct [P1↓]) (Ct [P2↓]) t t2 p).
         
       +++ now apply (t_being_tsilent_leads_to_contra  (Ct [P1↓]) (Ct [P2↓]) t t2 p).
         
       +++ destruct t2longer as [a t2longer].
           assert (xsem2 : xsem (Ct [P2↓]) (xtbd (snoc p a))) by now exists t2. 
           destruct (three_continuations_tbd p t xpref_x_t) as [ttstop | [ttsilent | ttlonger]].
           - destruct ttstop as [e ttstop].
             assert (xsem1 : xsem (Ct [P1↓]) (xstop p e)).
             { exists t. split; auto.
               rewrite ttstop. now apply xstop_prefix_list. }
             specialize (twoX (xstop p e) (xtbd (snoc p a)) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- inversion xpr1. 
             -- now apply xpr_longer_stop_contra in xpr2. 
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2 ]]]]]]].
                simpl in Hxpr1, Hxpr2. admit. (* contradiction from Hxpr1 and Hxpr2 *)        
           - assert (xsem1 : xsem (Ct [P1↓]) (xsilent p)).
             { exists t. split; auto.
               rewrite ttsilent. now apply xsilent_prefix_list. }
             specialize (twoX (xsilent p) (xtbd (snoc p a)) xsem1 xsem2).
             destruct twoX as [xpr1 | [xpr2 | matching]].
             -- inversion xpr1.
             -- now apply xpr_longer_silent_contra in xpr2. 
             -- destruct matching as [xx [i1 [i2 [Hi1 [Hi2 [Hdiff [Hxpr1 Hxpr2 ]]]]]]].
                simpl in Hxpr1, Hxpr2.  admit. (* contradiction from Hxpr1 and Hxpr2 *) 
           - destruct ttlonger as [aa ttlonger].
             now apply (violates_xmax (Ct [P1↓]) (Ct [P2↓]) t t2 p a aa).              
   ++ (*  it can only be t2 '=' xsilent p e = t *)
      apply (unique_continuation_silent p t) in xpref_x_t.
      apply (unique_continuation_silent p t2) in x_t2.
      congruence.
     
  + admit. (* symmetric case *)
Admitted. 

     
    