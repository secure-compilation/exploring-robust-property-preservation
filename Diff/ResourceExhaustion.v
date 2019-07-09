Require Import ClassicalExtras.

Require Import TraceModel.
Require Import Stream.
Require Import Properties.
Require Import Galois.

Require Import FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".


Section ResourceExhaustion.
  Variable event : Events.

  Variable endstate : Endstates.

  Definition endstateS : Endstates := endstate.

  Definition out_of_memory := unit.
  Definition endstateT : Endstates :=
    {| es := (es endstate + out_of_memory);
       an_es := inr tt
    |}.
  Definition OOM : es endstateT := inr tt.
  Hint Unfold OOM.

  Definition traceS := @trace event endstateS.
  Definition traceT := @trace event endstateT.
  Definition finprefS := @finpref event endstateS.
  Definition finprefT := @finpref event endstateT.

  Definition propS := @prop traceS.
  Definition propT := @prop traceT.
  Definition fpropS := @fprop event endstateS.
  Definition fpropT := @fprop event endstateT.

  Inductive syntactic_eq : traceS -> traceT -> Prop :=
  | syntactic_eq_tstop : forall l e,
      syntactic_eq (tstop l e) (tstop l ((inl e) : es endstateT))
  | syntactic_eq_tsilent : forall l,
      syntactic_eq (tsilent l) (tsilent l)
  | syntactic_eq_tstream : forall s,
      syntactic_eq (tstream s) (tstream s)
  .
  Notation "t__s '≡' t__t" := (syntactic_eq t__s t__t) (no associativity, at level 10).
  Hint Constructors syntactic_eq.

  Definition prefixTS (m__t : finprefT) (t__s : traceS) : Prop :=
    match m__t with
    | fstop l__t (inl e__t) =>
      match t__s with
      | tstop l__s e__s => e__t = e__s /\ l__t = l__s
      | _ => False
      end
    | fstop _ (inr _) => False
    | ftbd l__t =>
      match t__s with
      | tstop l__s _ | tsilent l__s => Stream.list_list_prefix l__t l__s
      | tstream s__s => Stream.list_stream_prefix l__t s__s
      end
    end.

  Definition rel : traceS -> traceT -> Prop :=
    fun t__s t__t => t__s ≡ t__t \/ exists m, (t__t = tstop m OOM /\ prefixTS (ftbd m) t__s).
  Hint Unfold rel.

  Inductive syntactic_eq_finpref : finprefS -> finprefT -> Prop :=
  | syntactic_eq_fstop : forall l e,
      syntactic_eq_finpref (fstop l e) (fstop l ((inl e) : es endstateT))
  | syntactic_eq_ftbd : forall l,
      syntactic_eq_finpref (ftbd l) (ftbd l)
  .

  (* Definition rel_finpref : finprefS -> finprefT -> Prop := *)
  (*   fun m__s m__t => syntactic_eq_finpref m__s m__t \/ exists l, (m__t = fstop l OOM /\ prefix_finpref (ftbd l) m__s). *)

  Definition GC_traceT_traceS : Galois_Connection traceT traceS :=
    induced_connection rel.

  Definition τ : propS -> propT := α GC_traceT_traceS.
  Definition σ : propT -> propS := γ GC_traceT_traceS.

  Lemma τ_preserves_dense : forall (π : propS),
      Dense π -> Dense (τ π).
  Proof.
    unfold Dense, τ, GC_traceT_traceS, induced_connection, low_rel; simpl.
    intros π HDense.
    intros t__t Hfin.
    destruct t__t as [l [e | []] | l | s].
    - exists (tstop l e). split.
      apply HDense. econstructor; eexists; eauto.
      left; eauto.
    - exists (tstop l (an_es endstateS)). split.
      apply HDense. econstructor; eexists; eauto.
      right; eexists; split; eauto.
      clear; simpl; induction l.
      reflexivity.
      now split.
    - destruct Hfin as [l' [e' Hn]].
      inversion Hn.
    - destruct Hfin as [l' [e' Hn]].
      inversion Hn.
  Qed.

  Lemma σ_preserves_dense : forall (π : propT),
      Dense π -> Dense (σ π).
  Proof.
    unfold Dense, σ, GC_traceT_traceS, induced_connection, up_rel; simpl.
    intros π HDense.
    intros t__s Hfin t__t Hrel.
    destruct Hrel as [Hrel | Hrel].
    - apply HDense; inversion Hrel; subst.
      + now repeat eexists.
      + destruct Hfin as [l' [e' Hn]].
        inversion Hn.
      + destruct Hfin as [l' [e' Hn]].
        inversion Hn.
    - destruct Hrel as [m [Heq Hpref]].
      apply HDense.
      rewrite Heq.
      now repeat eexists.
  Qed.


  (* The goal is now to prove that τ and/or σ preserve Safety.
   I need to define σ and τ for fprop, in order to use them
   to transform the set of bad prefixes *)
  Check Set.

  Definition trace_TS (t__t : traceT) : traceS :=
    match t__t with
    | tstop l (inl e) => tstop l e
    | tstop l (inr _) => tsilent l
    | tsilent l => tsilent l
    | tstream s => tstream s
    end.

  Lemma trace_TS_rel : forall (t__t : traceT),
      rel (trace_TS t__t) t__t.
  Proof.
    destruct t__t as [l [e | []] | l | s];
      try now left; constructor.
    - right.
      exists l.
      split.
      reflexivity.
      now induction l; split.
  Qed.

  Definition finpref_ST (m__s : finprefS) : finprefT :=
    match m__s with
    | fstop l e => fstop l (inl e : es endstateT) : finprefT
    | ftbd l => ftbd l
    end.


  Theorem τ_preserves_safety : forall (π : propS),
      Safety π -> Safety (τ π).
  Proof.
    unfold Safety, τ, GC_traceT_traceS, induced_connection, low_rel; simpl.
    intros π Hsafety t__t Ht.
    rewrite not_ex_forall_not in Ht;
      setoid_rewrite de_morgan1 in Ht;
      setoid_rewrite or_comm in Ht;
      setoid_rewrite <- imp_equiv in Ht.
    specialize (Hsafety (trace_TS t__t) (Ht (trace_TS t__t) (trace_TS_rel t__t))).
    destruct Hsafety as [m [Hpref H]].
    exists (finpref_ST m).
    split.
    - destruct m as [l e | l];
        destruct t__t as [l' [e' | []] | l' | s'];
        try now auto.
      now inversion Hpref; subst.
    - intros t__t' Hpref'.
      rewrite not_ex_forall_not;
        setoid_rewrite de_morgan1;
        setoid_rewrite or_comm;
        setoid_rewrite <- imp_equiv.
      intros t__s Hrel.
      apply H.
      destruct m as [l e | l].
      + destruct t__t' as [l' [e' | []] | l' | s'];
          try now auto.
        * destruct Hrel as [Hrel | Hrel].
          -- destruct t__s as [l'' e'' | l'' | s''];
               try now auto.
             inversion Hrel; subst.
             now inversion Hpref' as [H0 H1]; inversion H0; subst.
          -- destruct Hrel as [m [H1 H2]].
             now inversion H1.
        * destruct Hpref' as [H1 H2]; now inversion H1.
      + destruct t__t' as [l' [e' | []] | l' | s'];
          try now auto.
        * destruct Hrel as [Hrel | Hrel].
          -- destruct t__s as [l'' e'' | l'' | s''];
               try now auto.
             inversion Hrel; subst.
             now assumption.
          -- destruct Hrel as [m [H1 H2]].
             now inversion H1.
        * destruct Hrel as [Hrel | Hrel].
          -- destruct t__s as [l'' e'' | l'' | s''];
               try now auto.
          -- destruct Hrel as [m [H1 H2]]; try now auto.
             inversion H1; subst.
             simpl in Hpref'.
             destruct t__s as [l'' e'' | l'' | s''];
               try now eapply Stream.list_list_prefix_trans; eassumption.
             simpl in *.
             { clear -Hpref' H2.
               generalize dependent s''. generalize dependent m.
               induction l as [| e l]; intros m Hlm s Hms.
               - reflexivity.
               - destruct m as [| e' l'];
                   destruct Hlm;
                   subst.
                 destruct s as [e s].
                 simpl in *.
                 destruct Hms as [? Hl's]; subst.
                 split; first reflexivity.
                 now eapply IHl; eassumption.
             }
        * destruct Hrel as [Hrel | Hrel].
          -- destruct t__s as [l'' e'' | l'' | s''];
               try now auto.
             inversion Hrel; subst.
             assumption.
          -- destruct Hrel as [m [H1 H2]];
               try now auto.
        * destruct Hrel as [Hrel | Hrel].
          -- destruct t__s as [l'' e'' | l'' | s''];
               try now auto.
             inversion Hrel; subst.
             assumption.
          -- destruct Hrel as [m [H1 H2]];
               try now auto.
  Qed.

  Definition finpref_TS (m__t : finprefT) : finprefS :=
    match m__t with
    | fstop l (inl e) => fstop l e
    | fstop l (inr e) => ftbd l
    | ftbd l => ftbd l
    end.

  Definition trace_ST (t__s : traceS) : traceT :=
    match t__s with
    | tstop l e => tstop l (inl e : es endstateT)
    (* | tstop l e => tstop l OOM *)
    | tsilent l => tsilent l
    | tstream s => tstream  s
    end.

  Lemma rel_target_terminating (t__S : traceS)
        (l : list (ev event))
        (e : es endstate):
    rel t__S ((@tstop event endstateT l) ((inl out_of_memory e))) ->
    t__S = (@tstop event endstateS l e).
  Proof.
    destruct t__S; eauto; intros [rel_by_eq | [m [H1 H2]]];
      try now inversion rel_by_eq.
    + subst. now induction l.
    + now inversion H1.
    + now inversion H1.
  Qed.

  Lemma rel_tstop_OOM (l : list (ev event))
        (e : es endstateS):
    rel (tstop l e) (tstop l OOM).
  Proof.
    right. exists l. split; auto.
    now induction l.
  Qed.

  Lemma σ_preserves_safety : forall (π : propT),
      Safety π -> Safety (σ π).
  Proof.
    intros π__T safety_π__T t__S not_t__S.
    unfold σ, γ in not_t__S. simpl in not_t__S. unfold up_rel in not_t__S.
    rewrite not_forall_ex_not in not_t__S.
    destruct not_t__S as [t__T not_t__S]. rewrite not_imp in not_t__S.
    destruct not_t__S as [rel_ts_tt not_t__T].
    destruct (safety_π__T t__T not_t__T) as [m__T [pref_mt_tt mt_wit]].
    destruct m__T.
    + destruct es.
      ++ destruct t__T; inversion pref_mt_tt.
         apply prefix_stop_terminating_trace in pref_mt_tt.
         subst.
         assert (t__S = tstop l0 e) by now apply rel_target_terminating.
         subst.
         exists (fstop l0 e). split; try now auto.
         intros t__S' pref_m_t__S'.
         unfold σ, γ. simpl.  unfold up_rel. rewrite not_forall_ex_not.
         exists (@tstop event endstateT l0 (inl out_of_memory e)).
         rewrite not_imp. split; auto.
         apply prefix_stop_terminating_trace in pref_m_t__S'. now subst.
      ++ destruct t__T; inversion pref_mt_tt. subst.
         destruct rel_ts_tt as [Heq | [m [H1 H2]]].
         +++ inversion Heq.
         +++ rewrite H1 in *.
             exists (ftbd m). split; auto.
             intros t__S' Hpref'.  unfold σ, γ. simpl.  unfold up_rel. rewrite not_forall_ex_not.
             exists (tstop m OOM). rewrite not_imp.
             split; auto. right. now (exists m).
    + assert (prefix (ftbd l) (tstop l OOM)). { simpl; now apply  list_list_prefix_ref. }
                                              specialize (mt_wit (tstop l OOM) H).
      exists (ftbd l). split.
      ++ destruct rel_ts_tt as  [Heq | [m [H1 H2]]].
         +++ inversion Heq; subst; now simpl in *.
         +++ subst. destruct t__S; simpl in *.
             eapply list_list_prefix_trans. exact pref_mt_tt. exact H2.
             eapply list_list_prefix_trans. exact pref_mt_tt. exact H2.
             eapply list_stream_prefix_trans. exact pref_mt_tt. exact H2.
      ++ intros t__S' Hpref'.  unfold σ, γ. simpl.  unfold up_rel. rewrite not_forall_ex_not.
         exists (tstop l OOM). rewrite not_imp.
         split; auto. right. now exists l.
  Qed.

End ResourceExhaustion.
