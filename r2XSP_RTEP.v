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


Definition xsnoc (m : xpref) (e : event) :=
  match m with
  | xstop _ _ | xsilent _ => m
  | xtbd  l               => xtbd (snoc l e)
  end. 


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

Definition myXr (x1 x2: xpref) : Prop :=
  (xpr x1 x2) \/ (xpr x2 x1) \/
  (exists x i1 i2, is_input i1 /\
               is_input i2 /\
               i1 <> i2 /\
               xpr (xsnoc x i1) x1 /\
               xpr (xsnoc x i2) x2 /\
               xstopped x = false).


Lemma teq_premises_myXr_holds : forall P1 P2,
    (forall Cs t, sem src (Cs [P1]) t <-> sem src (Cs [P2]) t) ->
    (forall Cs x1 x2, xsem (Cs [P1]) x1 -> xsem (Cs [P2]) x2 ->
                 myXr x1 x2).
Proof.
  intros P1 P2 H Cs x1 x2 H0 H1. unfold myXr.
  assert (Hc :(xpr x1 x2 \/ xpr x2 x1) \/ ~ (xpr x1 x2 \/ xpr x2 x1)) by now apply classic.
  destruct Hc.
  + destruct H2; now auto.
  + destruct H0 as [b1 [H11 H12]].  destruct H1 as [b2 [H21 H22]].
    right. right.
Admitted.
(* CA: try to work on the lists of events to simplify things *)


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

Fixpoint list_to_silent_trace (l : list event) : trace :=
  match l with
  | nil => tsilent
  | cons l ls => tcons l (list_to_silent_trace ls)
  end.

Lemma unique_continuation_stop: forall l e t, xprefix (xstop l e) t -> t = list_to_stop_trace l e. 
Proof.
  intros l e. induction l.
  + intros [] Hxpref; auto; inversion Hxpref; now subst. 
  + intros [] Hxpref; inversion Hxpref. subst. 
    simpl. now rewrite (IHl t).    
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
    ++ destruct (three_continuations_tbd p t2 x_t2).
       +++ destruct (three_continuations_tbd p t xpref_x_t).
           - destruct H as [e2 H2]. destruct H0 as [e H].
             assert (xsem1 : xsem (Ct [P1↓]) (xstop p e)).
             { exists t. split; auto.
               rewrite H. now apply xstop_prefix_list. }
             assert (xsem2 : xsem (Ct [P2 ↓]) (xstop p e2)).
             { exists t2. split; auto.
               rewrite H2. now apply xstop_prefix_list. }    
             specialize (twoX (xstop p e) (xstop p e2) xsem1 xsem2). 
             destruct twoX as [xpr1 | [xpr2 | matching]]. 
             -- inversion xpr1. now subst.
             -- inversion xpr2. now subst.
             -- (* using matching deduce 
                   final events are input events,
                that shoul be a contraddiction *) admit. 
           -  destruct H0.
             -- destruct H as [e H].
                (* get a contraddiction from TwoX applied to (xstop p e) and (xslient p)
                   that are not in myXr
                 *) admit.
             -- (* get a contraddiction from TwoX applied to (xstop p e) and (xtbd (snoc p e))
                   that are not in myXr
                 *) admit.                  
       +++ destruct H.
           - admit. (* same story as above... 
                   
                     *)
           - admit. (* 
                      similar to above, in case of both snoc use input totality and 
                      get that p; e is also produced by P1, violating x_max
                     *)
             
   ++ (*  it can only be t2 '=' xsilent p e = t *)
      apply (unique_continuation_silent p t) in xpref_x_t.
      apply (unique_continuation_silent p t2) in x_t2.
      congruence.
     
  + admit. (* symmetric case *)
Admitted. 

     
    