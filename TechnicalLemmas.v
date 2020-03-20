Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import ClassicalExtras.

(** This file contains several lemmas that are used in other proofs *)

Lemma list_longest_in_psem {K : language} : forall (P' : prg K) l,
    exists ll, (list_list_prefix ll l) /\ (psem P' (ftbd ll)) /\
          (forall l', list_list_prefix l' l -> psem P' (ftbd l') -> list_list_prefix l' ll).
Proof.  
  intros P' l.
  induction l using list_ind_snoc.
  - exists nil; repeat (split; try now auto).
    + destruct (non_empty_sem K P') as [t Ht].
      exists t; split; simpl; auto. now case t. 
  - destruct IHl as [ll [Hprefll [Hpsem Hmaxll]]].
    destruct (classic (psem P' (ftbd (snoc l a)))) as [Hsnoc | Hsnoc].
    + exists (snoc l a).  repeat (split; try now auto).
      now apply list_list_prefix_ref. 
    + exists ll. repeat (split; try now auto).
      ++ simpl. now apply (list_prefix_snoc_list_prefix ll l a).
      ++ intros l' Hprefl' Hseml'.
         destruct (list_proper_or_equal l' (snoc l a)) as [Hequal | [aa Hproper]]; auto.
         +++ subst. contradiction.
         +++ apply list_pref_snoc_pref in Hproper.
             now apply (Hmaxll l').
Qed.

Lemma  longest_in_psem (tgt_sem : @semantics_safety_like tgt) :
  forall W t, ~ sem tgt W t ->
    exists m, prefix m t /\ psem W m /\
     (forall m', prefix m' t -> psem W m' -> fpr m' m).
Proof.
  intros W [] HsemWt.  
  + destruct (list_longest_in_psem W l) as [ll [Hpref [Hpsem Hmax]]].
    exists (ftbd ll). repeat (split; try now auto). 
    intros [] Hm Hsem.
    ++ inversion Hm; subst. destruct Hsem as [tm [Hprefmtm Hsemm]].
       destruct tm; inversion Hprefmtm; subst. contradiction.  
    ++ simpl in *. apply Hmax; auto. 
  + destruct (list_longest_in_psem W l) as [ll [Hpref [Hpsem Hmax]]].
    exists (ftbd ll). repeat (split; try now auto). 
    intros [] Hx Hsemx.
    ++ inversion Hx; subst.   
    ++ simpl in *. apply Hmax; auto. 
  + destruct (tgt_sem (tstream s) W) as [l [ebad [Hseml [Hprefl Hnsem_longer]]]]; auto. 
    exists (ftbd l). simpl in *. repeat (split; try now auto).
    ++ apply (list_stream_prefix_trans l (snoc l ebad) s); auto.
       now apply snoc_longer.
    ++ intros [] Hpref_x HxsemW; try now inversion Hpref_x.   
       simpl in *. destruct (list_stream_same_ext l0 (snoc l ebad) s); auto.
       * apply list_proper_or_equal in H. destruct H as [H | [a H]].
         ** subst. exfalso. apply Hnsem_longer. destruct HxsemW as [tx [H1 H2]]. 
                 now exists tx. 
         ** now apply list_pref_snoc_pref in H.
       * exfalso. apply Hnsem_longer. destruct HxsemW as [tx [H1 H2]].
             exists tx. split; try now auto.
             destruct tx; simpl in *; try now apply (list_list_prefix_trans (snoc l ebad) l0 l1). 
             now apply (list_stream_prefix_trans (snoc l ebad) l0 s0).
Qed.
