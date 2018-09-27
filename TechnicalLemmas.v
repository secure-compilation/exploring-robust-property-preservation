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


Lemma tapp_pref : forall m t t', t = tapp m t' -> prefix m t.
Proof.
  intros [].
  + induction p; intros t t' H.  
    ++ now rewrite H.
    ++ destruct t; try now inversion H.
       simpl. split; try now inversion H. 
       +++ apply (IHp t t'). now inversion H. 
  + induction p; intros t t' H.  
    ++ now rewrite H.
    ++ destruct t; try now inversion H.
       simpl. split; try now inversion H. 
       +++ apply (IHp t t'). now inversion H.
Qed.

Lemma prefix_fin_fpr : forall m mt t, prefix m t ->
                                 t = tapp mt tstop ->
                                 fstopped m = false ->
                                 fpr m mt.
Proof.
  intros []; induction p; intros [] t Hpref Happ Hstop; try now inversion Hstop.
  + destruct t; try now auto.
    inversion Hpref; subst. destruct p0; try now auto.
    inversion Happ. rewrite H1 in *.
    assert (foo : fstopped (ftbd p) = false) by auto.
    assert (app_foo : t = tapp (fstop p0) tstop) by auto. 
    specialize (IHp (fstop p0) t H0 app_foo foo). now auto.
  + destruct t; try now auto.
    inversion Hpref; subst. destruct p0; try now auto.
    inversion Happ. rewrite H1 in *.
    assert (foo : fstopped (ftbd p) = false) by auto.
    assert (app_foo : t = tapp (ftbd p0) tstop) by auto. 
    specialize (IHp (ftbd p0) t H0 app_foo foo). now auto.
Qed.   

Lemma stopped_pref_app : forall t m, prefix m t -> fstopped m = true ->
                                t = tapp m tstop.
Proof.
  intros t [] Hpref Hstop; try now inversion Hstop.
  generalize dependent t. induction p; intros [] Hpref; try now auto. 
  inversion Hpref; subst. assert (Hfoo : fstopped (fstop p) = true) by reflexivity.
  rewrite (IHp Hfoo t); auto. 
Qed.   

Lemma not_sem_psem_not_stopped {K : language} :
  forall W t m, ~ sem K W t -> prefix m t -> psem W m  -> fstopped m = false. 
Proof.
  intros W t m Hsemt Hpref Hpsem.
  destruct (fstopped m) eqn:Hstop; auto.
  apply stopped_pref_app in Hpref; auto. 
  destruct Hpsem as [t1 [H1 H2]].
  apply stopped_pref_app in H1; auto. now subst.
Qed.


Lemma longest_prefix_tstop {K : language} {HK : semantics_safety_like K} :
  forall W t, (exists m, t = tapp m tstop) -> ~ sem K W t ->
         (exists mm, prefix mm t /\ psem W mm /\
               (forall m', prefix m' t -> psem W m' -> fpr m' mm)).
Proof.
  intros W t [m Hm] Hsem.
  destruct (longest_in_psem W m) as [m0 [Hfpr [Hpsem [Hstopped Hm0]]]].
  assert (forall n, prefix n t -> psem W n -> fstopped n = false).
  { intros n H H0. now apply (not_sem_psem_not_stopped W t). }
  exists m0. repeat split;auto.
  - apply (fpr_pref_pref m0 m t); auto. now apply (tapp_pref m t tstop).
  - intros m' H0 H1. apply Hm0; auto. apply (prefix_fin_fpr m' m t); auto. 
Qed.   


Lemma fstopped_prefix_fpr : forall m m',
    (fstopped m = false -> prefix m' (tapp m tsilent) -> fpr m' m /\ fstopped m' = false).
Proof.
  intros m m'. generalize dependent m.
  induction finpref m' as e' p' IHp';
  intros [p | p] H1 H2; try now auto.
- simpl in H2. now destruct p.
- simpl in H2. destruct p as [|e p].
  + contradiction.
  + specialize (IHp' (ftbd p)). assert (fstopped (ftbd p) = false) by auto.
    specialize (IHp' H). simpl in *.
    destruct H2. specialize (IHp' H2). now destruct IHp'.
- destruct p as [|e p].
  + contradiction.
  + specialize (IHp' (ftbd p)). assert (fstopped (ftbd p) = false) by auto.
    specialize (IHp' H). simpl in *.
    destruct H2. specialize (IHp' H2). now destruct IHp'.
Qed.

Lemma continuum_lemma : forall m m' e1,
    fpr m m' -> fpr m' (fsnoc m e1) -> m = m' \/ m' = fsnoc m e1.
Proof.
  induction finpref m as e p IHp; intros; try now auto.
  - destruct finpref m' as e' p'; try now auto.
  - destruct finpref m' as e' p'; try now auto.
    inversion H; subst. now left.
  - destruct finpref m' as e' p'; try now auto.
    inversion H0; subst. simpl in *.
    assert (p' = nil) by now destruct p'.
    subst; now right.
  - destruct finpref m' as e' p'; try now auto.
    destruct H; subst.
    destruct H0; subst.
    specialize (IHp (ftbd p') e1 H1 H0).
    destruct IHp as [IHp | IHp]; inversion IHp; subst.
    now left.
    now right.
Qed.             

Lemma longest_prefix {K : language} {HK : semantics_safety_like K} :
  forall W t, ~ sem K W t ->
              (exists m, prefix m t /\ psem W m /\
                         (forall m', prefix m' t -> psem W m' -> fpr m' m)).
Proof.
  intros W t.
  (* apply longest_contra. *)
  intros H.
  destruct (fin_or_inf t) as [Ht | Ht].
  - (* fin t *)
    apply (@longest_prefix_tstop K HK W t).
    now apply (tapp_fin_pref t Ht). assumption. 
  - (* inf t *)
    destruct (classic (diverges t)) as [Ht' | Ht'].
    + (* diverges t *)
      pose proof (tapp_div_pref t Ht') as [m [Hnstopped Hsilent]].
      pose proof (longest_in_psem W m) as [mm [Hfpr [Hpsem [Hnstopped' Hmax]]]].
      subst.
      exists mm. repeat (split; auto).
      ++ apply fpr_pref_pref with (m2 := m).
         assumption.
         now apply tapp_pref with (t' := tsilent).
      ++ intros m' Hpref' Hpsem'.
         apply Hmax; auto;
         now destruct (fstopped_prefix_fpr m m' Hnstopped Hpref').
    + (* ~ diverges t *)
      unfold semantics_safety_like in HK.
      specialize (HK t W H Ht Ht').
      destruct HK as [m [ebad [Hpsem [Hpref Hnpsem]]]].
      exists m. repeat (split; auto).
      ++ apply fpr_pref_pref with (m2 := (fsnoc m ebad)).
         apply fpr_snoc_fpr. now apply fpr_reflexivity. assumption.
      ++ intros m' Hpref' Hpsem'.
         destruct (same_ext m' m t); auto.
         apply fpr_pref_pref with (m2 := (fsnoc m ebad)).
         apply fpr_snoc_fpr. now apply fpr_reflexivity. assumption.
         destruct (same_ext m' (fsnoc m ebad) t); try now auto.
         +++ destruct (continuum_lemma m m' ebad H0 H1); subst.
             now apply fpr_reflexivity.
             contradiction.
         +++ exfalso. apply Hnpsem.
             unfold psem in Hpsem'. destruct Hpsem' as [t' [Hm't' H'']].
             exists t'. split; try now auto.
             now apply fpr_pref_pref with (m2 := m').
Qed.

Lemma longest_prefix_safety_like : forall (K : language),
    (forall W t, ~ sem K W t ->
           (exists m, prefix m t /\ psem W m /\
                 (forall m', prefix m' t -> psem W m' -> fpr m' m)))
    -> semantics_safety_like K.
Proof.
  intros K HK.
  unfold semantics_safety_like.
  intros t W Hnsem Hinf Hndiv.
  specialize (HK W t Hnsem).
  destruct HK as [m [Hpref [Hpsem Hmax]]].
  assert (prefix m t -> inf t -> ~diverges t -> exists e, prefix (fsnoc m e) t).
  { clear. generalize dependent t.
    induction finpref m as e p IHp; intros t H H0 H1; try now eauto.
    - destruct t; try now eauto.
      + exfalso; apply H0. now constructor.
      + exfalso; apply H1. now constructor.
      + now (exists e).
    - destruct t; try now eauto.
      simpl in *. destruct H; subst.
      specialize (IHp t H2 (inf_tcons e0 t H0)).
      assert (~ diverges (tcons e0 t) -> ~ diverges t).
      { clear.
        destruct t; try now auto.
        - intros H. exfalso. apply H. constructor. constructor.
        - intros H. intros H'. apply H. now constructor. }
      specialize (IHp (H H1)).
      destruct IHp as [e He]. now (exists e).
  }
  destruct (H Hpref Hinf Hndiv) as [e He].
  exists m, e. repeat split; auto.
  intros Hn.
  specialize (Hmax (fsnoc m e) He Hn).
  assert (fstopped m = false -> fpr (fsnoc m e) m -> False).
  { clear.
    generalize dependent e.
    induction finpref m as e p IHp; intros; try now auto.
    simpl in *. destruct H0 as [_ H0].
    apply (IHp e0 H H0).
  }
  assert (inf t -> prefix m t -> fstopped m = false).
  { clear.
    generalize dependent t.
    induction finpref m as e p IHp; intros; try now auto.
    - destruct t; try now auto.
      exfalso. apply H. constructor.
    - destruct t; try now auto.
      simpl in *. destruct H0; subst.
      apply (IHp t (inf_tcons e0 t H) H1).
  }
  now apply (H0 (H1 Hinf Hpref) Hmax).
  Unshelve. 
  exact an_event.
  exact an_event.
  exact an_event.
  exact an_event.
Qed.

Theorem semantics_safety_like_equiv_longest_prefix : forall (K : language),
    semantics_safety_like K <-> (forall W t, ~ sem K W t ->
           (exists m, prefix m t /\ psem W m /\
                 (forall m', prefix m' t -> psem W m' -> fpr m' m))).
Proof.
  intros K; split.
  - intros HK; apply (@longest_prefix K HK).
  - intros HK; apply (longest_prefix_safety_like K HK).
Qed.
