Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import ClassicalExtras.

(* This file contains several lemmas that are used in other proofs *)

Lemma longest_in_psem {K : language} : forall (P' : prg K) m,
    exists mm, (fpr mm m) /\ (psem P' mm) /\
          (fstopped mm = false) /\
          (forall m', fpr m' m -> psem P' m'->  fstopped m' = false -> fpr m' mm).
Proof.
  intros P'.
  destruct m as [p | p]; induction p using pref_ind_snoc.
  - exists (ftbd nil); repeat (try split); try now auto.
    + unfold psem. pose proof (non_empty_sem K P').
      destruct H as [t Ht].
      exists t; split. reflexivity. assumption.
    + intros. destruct m'; now auto.
  - pose proof (classic (psem P' (ftbd (snoc p e)))). (* /!\ classic *)
    destruct H.
    + exists (ftbd (snoc p e)); repeat (try split).
      ++ now apply m_fpr_with_stop.
      ++ now assumption.
      ++ intros m' Hfpr Hpsem Hstopped.
         now destruct m'.
    + destruct IHp as [mm [Hfpr [Hsem [Hstopped H']]]].
      exists mm; repeat (try split); destruct mm as [pp | pp]; try now auto.
      ++ destruct (destruct_pref pp); try now subst.
         destruct H0 as [e' [m' Hsubst]]; subst.
         assert (Hfpr1 : fpr (ftbd (snoc m' e')) (ftbd p)).
         { clear H' Hstopped Hsem H. now assumption. }
         clear Hfpr.
         assert (Hfpr2 : fpr (ftbd p) (fstop (snoc p e))).
         { clear. now induction p. }
         apply (fpr_transitivity (ftbd (snoc m' e')) (ftbd p) (fstop (snoc p e))); now assumption.
      ++ intros m' Hm' Hsem' Hstopped'. destruct m' as [p' | p']; try now auto.
         specialize (H' (ftbd p')).
         assert (Hlemma : psem P' (ftbd p') ->
                          ~ (psem P' (ftbd (snoc p e))) ->
                          fpr (ftbd p') (ftbd (snoc p e)) ->
                          fpr (ftbd p') (fstop p)).
         { intros H0 H1 H2. unfold fpr in H2.
           apply destruct_fpr_ftbd_snoc in H2.
           destruct H2 as [H21 | H22].
           + subst p'. tauto.
           + assumption.
         }
         specialize (Hlemma Hsem' H Hm'). apply H'; assumption.
  - exists (ftbd nil); repeat (try split); try now auto.
    + unfold psem. pose proof (non_empty_sem K P').
      destruct H as [t Ht].
      exists t; split. reflexivity. assumption.
  - pose proof (classic (psem P' (ftbd (snoc p e)))). (* /!\ classic *)
    destruct H.
    + exists (ftbd (snoc p e)); repeat (try split).
      ++ now apply fpr_reflexivity.
      ++ now assumption.
      ++ intros m' Hfpr Hpsem Hstopped.
         now destruct m'.
    + destruct IHp as [mm [Hfpr [Hsem [Hstopped H']]]].
      exists mm; repeat (try split); destruct mm as [pp | pp]; try now auto.
      ++ destruct (destruct_pref pp); try now subst.
         destruct H0 as [e' [m' Hsubst]]; subst.
         assert (Hfpr1 : fpr (ftbd (snoc m' e')) (ftbd p)).
         { clear H' Hstopped Hsem H. now assumption. }
         clear Hfpr.
         assert (Hfpr2 : fpr (ftbd p) (fstop (snoc p e))).
         { clear. now induction p. }
         apply (fpr_transitivity (ftbd (snoc m' e')) (ftbd p) (fstop (snoc p e))); now assumption.
      ++ intros m' Hm' Hsem' Hstopped'. destruct m' as [p' | p']; try now auto.
         specialize (H' (ftbd p')).
         assert (Hlemma : psem P' (ftbd p') ->
                          ~ (psem P' (ftbd (snoc p e))) ->
                          fpr (ftbd p') (ftbd (snoc p e)) ->
                          fpr (ftbd p') (fstop p)).
         { intros H0 H1 H2. unfold fpr in H2.
           apply destruct_fpr_ftbd_snoc in H2.
           destruct H2 as [H21 | H22].
           + subst p'. tauto.
           + assumption.
         }
         specialize (Hlemma Hsem' H Hm'). apply H'; assumption.
Qed.
    
(* Informal proof: *)
(* By induction on the length of m, |m|.

  - Base case: |m| = 0.
    Then either m = ftbd or m = fstop.
    Let mm = ftbd. It is clear that (fpr ftbd m), that psem P' ftbd (because the semantics are not
    empty), that ftbd is not stopped.
    Let m' be a prefix of m, such that psem P' m' and m' is not stopped. Then, m' = ftbd.
    Hence the result.
  - Inductive case: let m be a finite prefix of length n + 1. Suppose the property is true
    for any finite prefix m' of length n' <= n.

    First, we can see that since m is of length n + 1, there exists m' such that |m'| = n,
    m' = m_1 ftbd, and m = m_1 e fstop or m = m_1 e ftbd.
    By induction hypothesis on m' of length n, there exists mm' such that fpr mm' m',
    psem P' mm', fstopped mm' = false, and
    (∀ m'', fpr m'' m' -> psem P' m''->  fstopped m'' = false -> fpr m'' mm').

    Let us consider two cases:
    + psem P' (m_1 e ftbd).
      Here, let mm = m_1 e ftbd (i.e. m, where the terminator is replaced by ftbd)
      ++ fpr m m therefore fpr (m_1 e ftbd) m
      ++ psem P' (m_1 e ftbd)
      ++ fstopped (m_1 e ftbd) = false
      ++ let m'' be such that fpr m'' m, psem P' m'', fstopped m'' = false.
         let us show that fpr m'' (m_1 e ftbd). This is true: any prefix of m that is not stopped
         is also a prefix of m where the terminator is replaced by ftbd.
    + ~ (psem P' (m_1 e ftbd))
      Let mm = mm'.
      ++ fpr mm' m' and fpr m' m so by transitivity fpr m'' m.
      ++ psem P' mm'
      ++ fstopped mm' = false
      ++ let m'' be such that fpr m'' m, psem P' m'', fstopped m'' = false.
         let us show that fpr m'' mm'.
         first, since ~(psem P' (m_1 e ftbd)), (psem P' mm'), and (fpr m'' m), we have that
         (fpr m'' (m_1 ftbd)) i.e. (fpr m'' m') By the induction hypothesis,
         we obtain the result, fpr m'' mm.
    Hence, the theorem is proved for any finite prefix m.
*)

(* TODO: TM#2 *)
Lemma a_technical_lemma: forall (P' : prg tgt) m,
    psem P' m ->
    (exists egood, psem P' (fsnoc m egood)) \/
     psem P' (m[fstop/ftbd]) \/
     (exists t, prefix m t /\ diverges t /\ sem tgt P' t).
Proof.
  intros P' m Hpsem. destruct (fstopped m) eqn:Hstop.
  + right. left. now rewrite <- if_fstopped_equal.
  + destruct Hpsem as [b [Hpref Hsem]].
    assert (embedding m = b \/ embedding m <> b) by now apply classic.
    destruct H as [H | H].
    ++ right. left. exists b. split; try now auto.
       rewrite <- H. rewrite embedding_is_the_same.
       now apply embed_pref.
    ++ assert (Hdiv : diverges b \/ ~ diverges b) by now apply classic.
       destruct Hdiv as [Hdiv | Hdiv].
       - right. right. now exists b.
       - left. destruct (proper_prefix m b Hpref H Hstop Hdiv) as [egood HH].
         now exists egood, b.
Qed.

Lemma longest_contra {K : language} :
  forall W t,
    ( ~ sem K W t ->
      (exists m, prefix m t /\ psem W m /\
            (forall m', prefix m' t -> psem W m' -> fpr m' m)))
    <->
    ((forall m, (psem W m /\ prefix m t) ->
           exists m', fpr m m' /\ m <> m' /\ prefix m' t /\ psem W m')
     -> sem K W t).
Proof.
  intros; split.
  - intros H.
    apply contra. intros Hsem; specialize (H Hsem).
    apply ex_not_not_all. destruct H as [m H].
    exists m.
    rewrite imp_equiv.
    apply de_morgan2. destruct H as [H1 [H2 H3]].
    split. rewrite <- dne; split; assumption.
    apply all_not_not_ex. intros n.
    apply de_morgan1. apply imp_equiv. intros Hfpr.
    apply de_morgan1. apply imp_equiv. intros Hneq. unfold not. intros Hpsem.
    destruct Hpsem.
    specialize (H3 n H H0).
    assert (Hi : fpr m n /\ fpr n m) by auto.
    pose proof (fpr_antisymmetry m n Hi). now subst.
  - intros H.
    apply contra. intros Hn.
    rewrite not_ex_forall_not in Hn.
    rewrite <- dne.
    apply H. intros m; specialize (Hn m).
    intros [H1 H2].
    apply de_morgan1 in Hn. rewrite <- imp_equiv in Hn.
    specialize (Hn H2).
    apply de_morgan1 in Hn. rewrite <- imp_equiv in Hn.
    specialize (Hn H1).
    rewrite not_forall_ex_not in Hn.
    destruct Hn as [m' Hm'].
    exists m'. rewrite -> imp_equiv in Hm'.
    apply de_morgan2 in Hm'. destruct Hm' as [Hm1' Hm2'].
    apply dne in Hm1'. rewrite -> imp_equiv in Hm2'.
    apply de_morgan2 in Hm2'. destruct Hm2' as [Hm2' Hm3'].
    apply dne in Hm2'.
    repeat (try split); try now assumption.
    + pose proof (same_ext m m' t H2 Hm1').
      now destruct H0.
    + unfold not; intros Hnot.
      subst. now pose proof (fpr_reflexivity m').
Qed.

Lemma longest_prefix_tstop {K : language} {HK : semantics_safety_like K} :
  forall W t, (exists m, t = tapp m tstop) -> ~ sem K W t ->
         (exists m, prefix m t /\ psem W m /\
               (forall m', prefix m' t -> psem W m' -> fpr m' m)).
Proof.
  intros W t [m Hm].
  apply longest_contra. intros H.
  unfold semantics_safety_like in HK.
Admitted.
    
    
  

Lemma longest_prefix {K : language} {HK : semantics_safety_like K} :
  forall W t, ~ sem K W t ->
              (exists m, prefix m t /\ psem W m /\
                         (forall m', prefix m' t -> psem W m' -> fpr m' m)).
Proof.
  intros W t.
  apply longest_contra.
  intros H.
  unfold semantics_safety_like in HK.
  rewrite dne. intros H'.
  specialize (HK t W H').
  destruct (classic (inf t)).
  - admit.
  - (* fin t *)
    unfold inf in H0; rewrite <- dne in H0.
    inversion H0.
    + (* tstop *)
      subst.
      specialize (H (ftbd nil)).
      assert (psem W (ftbd nil) /\ prefix (ftbd nil) tstop).
      { clear.
        split. pose proof (non_empty_sem K W). unfold psem. destruct H as [t Ht].
        exists t. split; auto. now destruct t.
        now auto.
      }
      specialize (H H1). destruct H as [m' [Hfpr [Hneq [Hpref Hpsem]]]].
      assert (Hc : m' = fstop nil).
      { clear HK H1 H' H0.
        now destruct finpref m' as e p.
      }
      subst.
      clear Hneq. clear Hfpr.
      clear Hpref.
      unfold psem in Hpsem.
      destruct Hpsem as [t [Hpref Hsem]].
      now destruct t.
    + 

Admitted.

  