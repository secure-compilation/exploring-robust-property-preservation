Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.
Require Import List.

Definition two_rRSC : Prop :=
  forall (r : finpref -> finpref -> Prop) P1 P2 ,
    ((forall Cs m1 m2, psem (Cs [P1]) m1 ->
                  psem (Cs [P2]) m2 ->
                   r m1 m2) ->
     (forall Ct m1 m2, psem (Ct [P1 ↓]) m1 ->
                  psem (Ct [P2 ↓]) m2 ->
                  r m1 m2)).


(** *our assumptions *)
(**********************************************************)
Hypothesis input_totality_tgt : input_totality tgt.
Hypothesis determinacy_src    : determinacy src.
Hypothesis tgt_sem            : semantics_safety_like tgt.
(**********************************************************)

Definition myr ( m1 m2 : finpref) : Prop :=
  (fpr m1 m2) \/ (fpr m2 m1) \/
  (exists m i1 i2,  is_input i1 /\
               is_input i2 /\
               i1 <> i2 /\
               fpr (fsnoc m i1) m1 /\
               fpr (fsnoc m i2) m2 /\
               fstopped m = false).

(*
   is we choose myr we can porve that
   the premises in teq_preservation hold
*)
Lemma teq_premises_myr_holds : forall P1 P2,
    (forall Cs t, sem src (Cs [P1]) t <-> sem src (Cs [P2]) t) ->
    (forall Cs m1 m2, psem (Cs [P1]) m1 -> psem (Cs [P2]) m2 ->
                 myr m1 m2).
Proof.
  intros P1 P2 H Cs m1 m2 H0 H1. unfold myr.
  assert (Hc :(fpr m1 m2 \/ fpr m2 m1) \/ ~ (fpr m1 m2 \/ fpr m2 m1)) by now apply classic.
  destruct Hc.
  + destruct H2; now auto.
  + destruct H0 as [b1 [H11 H12]].  destruct H1 as [b2 [H21 H22]].
    rewrite <- (H Cs b2) in H22. assert (Hdiff : b1 <> b2).
    { intros ff. subst. apply H2. now apply (same_ext m1 m2 b2). }
    right. right.
    destruct (determinacy_src (Cs [P1]) b1 b2 H12 H22) as [ff | K]; try now auto.
    destruct K as [m [e1 [e2 [He1 [He2 [Hdist [Hstop [Hp1 Hp2]]]]]]]].
    assert (Hcomp1 : fpr m1 (fsnoc m e1) \/ fpr (fsnoc m e1) m1) by now apply (same_ext _ _ b1).
    assert (Hcomp2 : fpr m2 (fsnoc m e2) \/ fpr (fsnoc m e2) m2) by now apply (same_ext _ _ b2).
    destruct Hcomp1, Hcomp2.
    ++ apply compare_with_snoc in H0. apply compare_with_snoc in H1.
       destruct H0, H1; try now auto.
       +++ exfalso. apply H2. now apply (same_fpr m1 m2 m).
       +++ exfalso. apply H2. apply (fpr_snoc_fpr m1 m e2) in H0. subst. now left.
       +++ exfalso. apply H2. apply (fpr_snoc_fpr m2 m e1) in H1. subst. now right.
       +++ exists m, e1, e2.
           repeat (split; try now auto); subst; apply fpr_reflexivity.
    ++ apply compare_with_snoc in H0. destruct H0.
       +++ exfalso. apply H2. apply (fpr_snoc_fpr m1 m e2) in H0. subst. left.
           now apply (fpr_transitivity m1 (fsnoc m e2) m2).
       +++ exists m, e1, e2. repeat (split; try now auto); subst; apply fpr_reflexivity.
    ++ apply compare_with_snoc in H1. destruct H1.
       +++ exfalso. apply H2. apply (fpr_snoc_fpr m2 m e1) in H1. subst. right.
           now apply (fpr_transitivity m2 (fsnoc m e1) m1).
       +++ exists m, e1, e2. repeat (split; try now auto); subst; apply fpr_reflexivity.
    ++ now exists m, e1, e2.
Qed.

Lemma longest_in_psem : forall (P' : prg tgt) m,
    exists mm, (fpr mm m) /\ (psem P' mm) /\
          (fstopped mm = false) /\
          (forall m', fpr m' m -> psem P' m'->  fstopped m' = false -> fpr m' mm).
Proof.
  intros P'.
  destruct m as [p | p]; induction p using pref_ind_snoc.
  - exists (ftbd nil); repeat (try split); try now auto.
    + unfold psem. pose proof (non_empty_sem tgt P').
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
    + unfold psem. pose proof (non_empty_sem tgt P').
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

Hypothesis no_divergence : forall P' t, sem tgt P' t -> ~ diverges t.
Theorem two_rRSC_teq : two_rRSC -> teq_preservation.
Proof.
  unfold two_rRSC, teq_preservation. intros twoR P1 P2 H0 Ct t.
  apply NNPP. intros ff. rewrite not_iff in ff.
  destruct ff as [[f0 f1] | [f0 f1]].
  + specialize (twoR myr P1 P2 (teq_premises_myr_holds P1 P2 H0)).
     destruct (fin_or_inf t) as [Hfin | Hinf].
    ++ apply fin_equal in Hfin. destruct Hfin as [m Hm].
       destruct (longest_in_psem  (Ct [P2 ↓]) m) as [mm [Hfpr [Hpsem2 [Hstopmm Hmax]]]].
       destruct Hpsem2 as [t2 [Hpref2 Hsem2]].
       assert (H : (embedding mm) = t2 \/ (embedding mm) <> t2) by now apply classic.
       destruct H as [Ht2t | H].
       * assert (embedding m <> embedding mm).
         { intros ff. apply equal_embedding in Hm. subst. now rewrite <- ff in Hsem2. }
         destruct (twoR Ct m (mm[fstop/ftbd])).
         ** exists t. split; try now auto. now apply equal_prefix.
         ** exists t2. split; try now auto. rewrite <- Ht2t. now apply with_stop_prefix_embedding.
         ** apply H. apply (equal_stopped m t) in Hm.
            now apply equal_with_stop_same_embedding.
         ** destruct H1 as [H1 | H1].
            *** apply H. assert (Heq : mm[fstop/ftbd] = m).
                { apply (fpr_stop_equal (mm[fstop/ftbd]) m); try now auto.
                  now apply with_stop_fstopped. }
                rewrite (embedding_is_the_same mm) in *. now rewrite <- Heq.
            *** destruct H1 as [m0 [i1 [i2 [Hin1 [Hin2 [Hdiffi [Hfpr1 [Hfpr2 Hstop0]]]]]]]].
                apply (proper_fpr (fsnoc m0 i2) mm) in Hfpr2; try now auto.
                apply (fpr_transitivity (fsnoc m0 i2) mm m Hfpr2) in Hfpr; try now auto.
                destruct (same_fpr (fsnoc m0 i1) (fsnoc m0 i2) m)
                  as [Hfalse | Hfalse]; try now auto.
                now apply (snoc_m_event_equal m0 i1 i2) in Hfalse; auto.
                apply (snoc_m_event_equal m0 i2 i1) in Hfalse; congruence.
                now apply snoc_stop.
       * destruct (proper_prefix mm t2) as [e He]; try now auto.
         eapply no_divergence; eassumption.
         assert (Hnot : ~ fpr (fsnoc mm e) m).
         { intros ff. assert (Hfoo1 : psem (Ct [P2 ↓]) (fsnoc mm e)) by now exists t2.
           assert (Hfoo2 : (fstopped (fsnoc mm e) = false)) by now apply snoc_stop.
           specialize (Hmax (fsnoc mm e) ff Hfoo1 Hfoo2).
           now apply (not_stop_not_snoc_pref mm e). }
         destruct (twoR Ct m (fsnoc mm e)) as [K1 | [K2 | K3]]; try now auto.
         exists t. split; auto. now apply (equal_prefix m t).
         now exists t2.
         assert (fstopped m = true) by now apply (equal_stopped m t).
         assert (m = fsnoc mm e) by now apply fpr_stop_equal. now subst.
         destruct K3 as [m0 [i1 [i2 [Hin1 [Hin2 [Hdiffi [Hfpr1 [Hfpr2 Hstop0]]]]]]]].
         assert ((fpr (fsnoc m0 i2)) mm \/ (fsnoc m0 i2) = fsnoc mm e) by
             now apply (compare_with_snoc (fsnoc m0 i2) mm e).
         destruct H1.
         ** apply (fpr_transitivity (fsnoc m0 i2) mm m) in H1; try now auto.
            apply (same_fpr (fsnoc m0 i1) (fsnoc m0 i2) m Hfpr1) in H1.
            destruct H1; apply Hdiffi;
              [now apply (snoc_diff m0 i1 i2) | symmetry; now apply (snoc_diff m0 i2 i1) ].
         ** apply same_snoc_same_pointwise in H1; try now auto.
            destruct H1 as [Heq1 Heq2].
            subst.
            assert (psem (Ct [P2 ↓]) (fsnoc mm i1)).
            { apply (input_totality_tgt ((Ct [P2 ↓])) mm e i1); try now auto.
            now exists t2. }
            rewrite <- snoc_stop in Hstop0. specialize (Hmax (fsnoc mm i1) Hfpr1 H1 Hstop0).
            now apply (not_stop_not_snoc_pref mm i1).
    ++ destruct (non_empty_sem tgt (Ct [P2 ↓])) as [b Hb].
       destruct t,b; try now auto.
       * eapply no_divergence in Hb. apply Hb. constructor.
       * (* destruct (twoR Ct (fstop) (fcons e ftbd)); try now auto. *)
         destruct (twoR Ct (fstop nil) (ftbd (cons e nil))); try now auto.
         now exists tstop. now exists (tcons e b). destruct H; try now auto.
         destruct H as [m [i1 [i2 [H1 [H2 [Hdiff [Hp1 [Hp2 Hstop]]]]]]]]. 
         destruct m as [m | m]; now destruct m.
       * eapply no_divergence in f0. apply f0. constructor.
       * eapply no_divergence in f0. apply f0. constructor.
       * (* destruct (twoR Ct (fcons e ftbd) (fstop)); try now auto. *)
         destruct (twoR Ct (ftbd (cons e nil)) (fstop nil)); try now auto.
         now (exists (tcons e t)). now (exists tstop). destruct H; try now auto.
         destruct H as [m [i1 [i2 [H1 [H2 [Hdiff [Hp1 [Hp2 Hstop]]]]]]]]. 
         destruct m as [m | m]; now destruct m.
       * eapply no_divergence in Hb. apply Hb. constructor.
       * destruct (tgt_sem (tcons e t) (Ct [P2 ↓]) f1 Hinf) as
                     [m [ebad [Hpsemm [Hpref Hpsem']]]]. eapply no_divergence; eassumption.
         assert ( (exists egood,                           psem     (Ct [P2 ↓]) (fsnoc m egood)) \/
                                                      psem     (Ct [P2 ↓]) (m[fstop/ftbd])  \/
                  (exists t,     prefix m t /\ diverges t /\  sem tgt (Ct [P2 ↓]) t))
           by now apply a_technical_lemma.
        destruct H as [k1 | k2].
        ** destruct k1 as [egood Hpsem].
            assert (fstopped m = false \/ fstopped m = true) by
               (destruct (fstopped m); now auto).
            destruct H as [K | K].
         -- destruct (twoR Ct (fsnoc m ebad) (fsnoc m egood)) as [H | [H | H]]; try now auto.
            now exists (tcons e t). apply snoc_m_event_equal in H. now subst. assumption.
            apply snoc_m_event_equal in H. now subst. assumption.
            destruct H as  [m' [i1 [i2 [H1 [H2 [Hdiff [Hp1 [Hp2 Hstop]]]]]]]].
            destruct (same_snoc_same_finpref m m' egood ebad i2 i1); try now auto.
            intros ff. now subst.
            apply snoc_diff in Hp1; try now auto.
            apply snoc_diff in Hp2; try now auto.  subst.
             specialize (input_totality_tgt (Ct [P2 ↓]) m' egood ebad); try now auto.
         -- specialize (stop_snoc_id m ebad K).
            specialize (stop_snoc_id m egood K).
            intros H3 H4. rewrite H3 in Hpsem. now rewrite H4 in Hpsem'.
        ** destruct k2 as [k2 | [t' [k21 [k22 k23]]]].
           - destruct (twoR Ct  (fsnoc m ebad) (m[fstop/ftbd])) as [H | [H | H]]; try now auto.
             now exists (tcons e t).
             apply Hpsem'. destruct k2 as [x [Hx HHx]]. exists x. split; try now auto.
             now apply (fpr_pref_pref (fsnoc m ebad) (m[fstop/ftbd]) x).
             apply fpr_stop_equal in H. now rewrite <- H in Hpsem'.
             now apply with_stop_fstopped.
             destruct H as  [m' [i1 [i2 [H1 [H2 [Hdiff [Hp1 [Hp2 Hstop]]]]]]]].
             apply proper_fpr in Hp2; try apply with_stop_fstopped; try (now apply snoc_stop).
             apply compare_with_snoc in Hp1. destruct Hp1 as [K1 | K2].
             apply (same_fpr (fsnoc m' i1) (fsnoc m' i2) m K1) in Hp2.
             destruct Hp2 as [Hp | Hp]; apply snoc_m_event_equal in Hp; now congruence.
             assert (fstopped m = false).
             { destruct (fstopped m) eqn : Hm; try now auto.
               rewrite (stop_snoc_id m ebad) in K2; try now auto.
               rewrite <- K2 in Hp2. apply snoc_m_event_equal in Hp2; auto.
               congruence. }
             apply same_snoc_same_pointwise in K2; try now auto.
             destruct K2 as [K21 K22]. rewrite K21 in Hp2.
             now apply not_stop_not_snoc_pref in Hp2.
           - apply no_divergence in k23. contradiction.
 + assert (Hsymm0 : forall (Cs : ctx src) (t : trace), sem src (Cs [P2]) t <-> sem src (Cs [P1]) t)
          by now firstorder.
   specialize (twoR myr P2 P1 (teq_premises_myr_holds P2 P1 Hsymm0)).
     destruct (fin_or_inf t) as [Hfin | Hinf].
    ++ apply fin_equal in Hfin. destruct Hfin as [m Hm].
       destruct (longest_in_psem  (Ct [P1 ↓]) m) as [mm [Hfpr [Hpsem2 [Hstopmm Hmax]]]].
       destruct Hpsem2 as [t2 [Hpref2 Hsem2]].
       assert (H : (embedding mm) = t2 \/ (embedding mm) <> t2) by now apply classic.
       destruct H as [Ht2t | H].
       * assert (embedding m <> embedding mm).
         { intros ff. apply equal_embedding in Hm. subst. now rewrite <- ff in Hsem2. }
         destruct (twoR Ct m (mm[fstop/ftbd])).
         ** exists t. split; try now auto. now apply equal_prefix.
         ** exists t2. split; try now auto. rewrite <- Ht2t. now apply with_stop_prefix_embedding.
         ** apply H. apply (equal_stopped m t) in Hm.
            now apply equal_with_stop_same_embedding.
         ** destruct H1 as [H1 | H1].
            *** apply H. assert (Heq : mm[fstop/ftbd] = m).
                { apply (fpr_stop_equal (mm[fstop/ftbd]) m); try now auto.
                  now apply with_stop_fstopped. }
                rewrite (embedding_is_the_same mm) in *. now rewrite <- Heq.
            *** destruct H1 as [m0 [i1 [i2 [Hin1 [Hin2 [Hdiffi [Hfpr1 [Hfpr2 Hstop0]]]]]]]].
                apply (proper_fpr (fsnoc m0 i2) mm) in Hfpr2; try now auto.
                apply (fpr_transitivity (fsnoc m0 i2) mm m Hfpr2) in Hfpr; try now auto.
                destruct (same_fpr (fsnoc m0 i1) (fsnoc m0 i2) m)
                  as [Hfalse | Hfalse]; try now auto.
                now apply (snoc_m_event_equal m0 i1 i2) in Hfalse; auto.
                apply (snoc_m_event_equal m0 i2 i1) in Hfalse; congruence.
                now apply snoc_stop.
       * destruct (proper_prefix mm t2) as [e He]; try now auto.
         eapply no_divergence; eassumption.
         assert (Hnot : ~ fpr (fsnoc mm e) m).
         { intros ff. assert (Hfoo1 : psem (Ct [P1 ↓]) (fsnoc mm e)) by now exists t2.
           assert (Hfoo2 : (fstopped (fsnoc mm e) = false)) by now apply snoc_stop.
           specialize (Hmax (fsnoc mm e) ff Hfoo1 Hfoo2).
           now apply (not_stop_not_snoc_pref mm e). }
         destruct (twoR Ct m (fsnoc mm e)) as [K1 | [K2 | K3]]; try now auto.
         exists t. split; auto. now apply (equal_prefix m t).
         now exists t2.
         assert (fstopped m = true) by now apply (equal_stopped m t).
         assert (m = fsnoc mm e) by now apply fpr_stop_equal. now subst.
         destruct K3 as [m0 [i1 [i2 [Hin1 [Hin2 [Hdiffi [Hfpr1 [Hfpr2 Hstop0]]]]]]]].
         assert ((fpr (fsnoc m0 i2)) mm \/ (fsnoc m0 i2) = fsnoc mm e) by
             now apply (compare_with_snoc (fsnoc m0 i2) mm e).
         destruct H1.
         ** apply (fpr_transitivity (fsnoc m0 i2) mm m) in H1; try now auto.
            apply (same_fpr (fsnoc m0 i1) (fsnoc m0 i2) m Hfpr1) in H1.
            destruct H1; apply Hdiffi;
              [now apply (snoc_diff m0 i1 i2) | symmetry; now apply (snoc_diff m0 i2 i1) ].
         ** apply same_snoc_same_pointwise in H1; try now auto.
            destruct H1 as [Heq1 Heq2].
            subst.
            assert (psem (Ct [P1 ↓]) (fsnoc mm i1)).
            { apply (input_totality_tgt ((Ct [P1 ↓])) mm e i1); try now auto.
            now exists t2. }
            rewrite <- snoc_stop in Hstop0. specialize (Hmax (fsnoc mm i1) Hfpr1 H1 Hstop0).
            now apply (not_stop_not_snoc_pref mm i1).
    ++ destruct (non_empty_sem tgt (Ct [P1 ↓])) as [b Hb].
       destruct t,b; try now auto.
       * eapply no_divergence in Hb. apply Hb. constructor.
       * (* destruct (twoR Ct (fstop) (fcons e ftbd)); try now auto. *)
         destruct (twoR Ct (fstop nil) (ftbd (cons e nil))); try now auto.
         now (exists tstop). now (exists (tcons e b)). destruct H; try now auto.
         destruct H as [m [i1 [i2 [H1 [H2 [Hdiff [Hp1 [Hp2 Hstop]]]]]]]].
         destruct m as [m | m]; now destruct m.
       * eapply no_divergence in f1. apply f1. constructor.
       * eapply no_divergence in f1. apply f1. constructor.
       * (* destruct (twoR Ct (fcons e ftbd) (fstop)); try now auto. *)
         destruct (twoR Ct (ftbd (cons e nil)) (fstop nil)); try now auto.
         now (exists (tcons e t)). now (exists tstop). destruct H; try now auto.
         destruct H as [m [i1 [i2 [H1 [H2 [Hdiff [Hp1 [Hp2 Hstop]]]]]]]]. 
         destruct m as [m | m]; now destruct m.
       * eapply no_divergence in Hb. apply Hb. constructor.
       * destruct (tgt_sem (tcons e t) (Ct [P1 ↓]) f0 Hinf) as
                     [m [ebad [Hpsemm [Hpref Hpsem']]]]. eapply no_divergence; eassumption.
         assert ( (exists egood,                           psem     (Ct [P1 ↓]) (fsnoc m egood)) \/
                                                      psem     (Ct [P1 ↓]) (m[fstop/ftbd])  \/
                  (exists t,     prefix m t /\ diverges t /\  sem tgt (Ct [P1 ↓]) t))
           by now apply a_technical_lemma.
        destruct H as [k1 | k2].
        ** destruct k1 as [egood Hpsem].
            assert (fstopped m = false \/ fstopped m = true) by
               (destruct (fstopped m); now auto).
            destruct H as [K | K].
         -- destruct (twoR Ct (fsnoc m ebad) (fsnoc m egood)) as [H | [H | H]]; try now auto.
            now exists (tcons e t). apply snoc_m_event_equal in H. now subst. assumption.
            apply snoc_m_event_equal in H. now subst. assumption.
            destruct H as  [m' [i1 [i2 [H1 [H2 [Hdiff [Hp1 [Hp2 Hstop]]]]]]]].
            destruct (same_snoc_same_finpref m m' egood ebad i2 i1); try now auto.
            intros ff. now subst.
            apply snoc_diff in Hp1; try now auto.
            apply snoc_diff in Hp2; try now auto.  subst.
             specialize (input_totality_tgt (Ct [P1 ↓]) m' egood ebad); try now auto.
         -- specialize (stop_snoc_id m ebad K).
            specialize (stop_snoc_id m egood K).
            intros H3 H4. rewrite H3 in Hpsem. now rewrite H4 in Hpsem'.
        ** destruct k2 as [k2 | [t' [k21 [k22 k23]]]].
           - destruct (twoR Ct  (fsnoc m ebad) (m[fstop/ftbd])) as [H | [H | H]]; try now auto.
             now exists (tcons e t).
             apply Hpsem'. destruct k2 as [x [Hx HHx]]. exists x. split; try now auto.
             now apply (fpr_pref_pref (fsnoc m ebad) (m[fstop/ftbd]) x).
             apply fpr_stop_equal in H. now rewrite <- H in Hpsem'.
             now apply with_stop_fstopped.
             destruct H as  [m' [i1 [i2 [H1 [H2 [Hdiff [Hp1 [Hp2 Hstop]]]]]]]].
             apply proper_fpr in Hp2; try apply with_stop_fstopped; try (now apply snoc_stop).
             apply compare_with_snoc in Hp1. destruct Hp1 as [K1 | K2].
             apply (same_fpr (fsnoc m' i1) (fsnoc m' i2) m K1) in Hp2.
             destruct Hp2 as [Hp | Hp]; apply snoc_m_event_equal in Hp; now congruence.
             assert (fstopped m = false).
             { destruct (fstopped m) eqn : Hm; try now auto.
               rewrite (stop_snoc_id m ebad) in K2; try now auto.
               rewrite <- K2 in Hp2. apply snoc_m_event_equal in Hp2; auto.
               congruence. }
             apply same_snoc_same_pointwise in K2; try now auto.
             destruct K2 as [K21 K22]. rewrite K21 in Hp2.
             now apply not_stop_not_snoc_pref in Hp2.
           - apply no_divergence in k23. contradiction.
Qed.
