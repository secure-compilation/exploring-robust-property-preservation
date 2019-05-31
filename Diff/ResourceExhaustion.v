Require Import ClassicalExtras.

Require Import TraceModel.
Require Import Properties.
Require Import Galois.

Set Bullet Behavior "Strict Subproofs".

(* This file is intentionaly NOT included in _CoqProject *)


Axiom event : Events.

Axiom endstate : Endstates.

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

Definition no_OOM : propT :=
  fun t__t => not (exists l, t__t = tstop l OOM).

Lemma σ_no_OOM : Safety (σ (no_OOM)).
Proof.
  unfold no_OOM, σ, GC_traceT_traceS, induced_connection, up_rel; simpl.
  unfold Safety.
  intros t__s H.
  setoid_rewrite not_forall_ex_not in H;
    setoid_rewrite not_imp in H;
    setoid_rewrite <- dne in H.
  destruct H as [t__t [Hrel [m Ht__t]]]; subst.
  destruct Hrel as [Hrel | Hrel].
  - now inversion Hrel.
  - destruct Hrel as [m' [Heq Hpref]];
      inversion Heq; subst m'.
    exists (ftbd m).
    split; first assumption.
    intros t__s' Hpref' Hn.
    specialize (Hn (tstop m OOM)).
    assert (rel t__s' (tstop m OOM)) by now eauto.
    specialize (Hn H).
    rewrite not_ex_forall_not in Hn.
    now specialize (Hn m).
Qed.

Definition stop_implies_OOM : propT :=
  fun t__t => exists l e, t__t = tstop l e -> e = OOM.

Lemma σ_stop_implies_OOM : Safety (σ (stop_implies_OOM)).
Proof.
  unfold stop_implies_OOM, σ, GC_traceT_traceS, induced_connection, up_rel;
    simpl.
  unfold Safety.
  intros t__s H.
  setoid_rewrite not_forall_ex_not in H;
    setoid_rewrite not_imp in H;
    setoid_rewrite not_ex_forall_not in H;
    setoid_rewrite not_ex_forall_not in H;
    setoid_rewrite not_imp in H.
  destruct H as [t__t [Hrel H]].
  now destruct (H nil OOM) as [_ Hn].
Qed.

Definition stop_implies_not_OOM : propT :=
  fun t__t => exists l e, t__t = tstop l e -> e <> OOM.

Lemma σ_stop_implies_not_OOM : Safety (σ (stop_implies_not_OOM)).
Proof.
  unfold stop_implies_not_OOM, σ, GC_traceT_traceS;
  unfold induced_connection, up_rel;
    simpl.
  unfold Safety.
  intros t__s H.
  setoid_rewrite not_forall_ex_not in H;
    setoid_rewrite not_imp in H;
    setoid_rewrite not_ex_forall_not in H;
    setoid_rewrite not_ex_forall_not in H;
    setoid_rewrite not_imp in H.
  destruct H as [t__t [Hrel H]].
  destruct (H nil (inl (an_es endstateS) : es endstateT)) as [_ Hn].
  now rewrite <- dne in Hn.
Qed.

Definition stops_now : propT :=
  fun t__t => (exists e, t__t = tstop nil e) \/ t__t = tsilent nil.


Lemma stops_now_safety : Safety (stops_now).
Proof.
  unfold stops_now, Safety.
  intros t__t Hn.
  setoid_rewrite de_morgan2 in Hn;
    setoid_rewrite not_ex_forall_not in Hn.
  destruct Hn as [Hn1 Hn2].
  destruct t__t as [[| ev l] es | l | s].
  - now specialize (Hn1 es).
  - exists (ftbd (ev::l)).
    split.
    + split; first reflexivity; now apply Stream.list_list_prefix_ref.
    + intros t__t' Hpref.
      setoid_rewrite de_morgan2;
        setoid_rewrite not_ex_forall_not.
      split.
      intros es'.
      destruct t__t' as [[| ev'' l''] es'' | l'' | s''];
        try now auto.
      destruct t__t' as [[| ev'' l''] es'' | [| ev'' l''] | s''];
        try now auto.
  - destruct l as [| ev l]; try now auto.
    exists (ftbd (ev::l)).
    split.
    + split; first reflexivity; now apply Stream.list_list_prefix_ref.
    + intros t__t' Hpref.
      setoid_rewrite de_morgan2;
        setoid_rewrite not_ex_forall_not.
      split.
      intros es'.
      destruct t__t' as [[| ev'' l''] es'' | l'' | s''];
        try now auto.
      destruct t__t' as [[| ev'' l''] es'' | [| ev'' l''] | s''];
        try now auto.
  - destruct s as [ev s].
    exists (ftbd (ev::nil)).
    split.
    + split; reflexivity.
    + intros t__t' Hpref.
      setoid_rewrite de_morgan2;
        setoid_rewrite not_ex_forall_not.
      split.
      intros es'.
      destruct t__t' as [[| ev'' l''] es'' | l'' | s''];
        try now auto.
      destruct t__t' as [[| ev'' l''] es'' | [| ev'' l''] | s''];
        try now auto.
Qed.

Lemma σ_stops_now : Safety (σ stops_now).
Proof.
  unfold stops_now, σ, GC_traceT_traceS;
  unfold induced_connection, up_rel;
    simpl.
  unfold Safety.
  intros t__s H.
  setoid_rewrite not_forall_ex_not in H;
    setoid_rewrite not_imp in H;
    setoid_rewrite de_morgan2 in H;
    setoid_rewrite not_ex_forall_not in H.
  destruct H as [t__t [Hrel [H1 H2]]].
  destruct Hrel as [Hrel | Hrel].
  - destruct Hrel; try now auto.
    + destruct l as [| e' l']; first now specialize (H1 (inl e)).
      exists (ftbd (e' :: l')).
      split. split; first reflexivity; now apply Stream.list_list_prefix_ref.
      intros t__s Hpref Hn.
      destruct t__s as [[| e'' l''] estate | [| e'' l'' ] | [e'' s'']];
        try now auto.
      * specialize (Hn (tstop (e'' :: l'') (inl estate : es endstateT ))).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        inversion Hee.
        inversion Hn.
      * specialize (Hn (tsilent (e'' :: l''))).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        inversion Hee. inversion Hn.
      * specialize (Hn (tstream (Stream.scons e'' s''))).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        inversion Hee. inversion Hn.
    + destruct l as [|]; try now auto.
      exists (ftbd (e :: l)).
      split. split; first reflexivity; now apply Stream.list_list_prefix_ref.
      intros t__s Hpref Hn.
      destruct t__s as [[| e'' l''] estate | [| e'' l'' ] | [e'' s'']];
        try now auto.
      * specialize (Hn (tstop (e'' :: l'') (inl estate : es endstateT ))).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        inversion Hee.
        inversion Hn.
      * specialize (Hn (tsilent (e'' :: l''))).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        inversion Hee. inversion Hn.
      * specialize (Hn (tstream (Stream.scons e'' s''))).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        inversion Hee. inversion Hn.
    + destruct s as [e s].
      exists (ftbd (e::nil)).
      split. split; reflexivity.
      intros t__s Hpref Hn.
      destruct t__s.
      * specialize (Hn (tstop l (inl e0 : es endstateT))).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        now inversion Hee; subst.
        inversion Hn.
      * specialize (Hn (tsilent l)).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        now inversion Hee.
        now inversion Hn; subst.
      * specialize (Hn (tstream s0)).
        destruct Hn as [[ee Hee] | Hn]; eauto.
        inversion Hee.
        inversion Hn.
  - destruct Hrel as [l [H3 H4]]; subst.
    destruct l as [| e l]; first now specialize (H1 OOM).
    clear H1 H2.
    exists (ftbd (e::l)).
    split. simpl in *. assumption.
    intros t__s' Hpref Hn.
    destruct t__s'.
    * specialize (Hn (tstop l0 (inl e0 : es endstateT))).
      destruct Hn as [[ee Hee] | Hn]; eauto.
      now inversion Hee; subst.
      inversion Hn.
    * specialize (Hn (tsilent l0)).
      destruct Hn as [[ee Hee] | Hn]; eauto.
      now inversion Hee.
      now inversion Hn; subst.
    * specialize (Hn (tstream s)).
      destruct Hn as [[ee Hee] | Hn]; eauto.
      inversion Hee.
      inversion Hn.
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
  + (* CA: in case mT = fstop l es, rel ts tT -> ts = tT
           (prove a separate lemma for this)
           and hence one just has to pick ms = mT
     
       CA: in case mT = fstop l out_of_memory then every source continuation of 
           mT is still related with tT, so it is not in σ(πT)

    *) admit.
        
  + (* CA: in case mT = ftbd l, 
           then mT < tT and mT <= ts.
           In particular tT' = mT;out_of_mem ∉ πT.
           Notice that ∀ tS' > mT, rel tS' tT', hence tS' ∉ σ(πT).
     *) admit.
Admitted. 
        
  
 (*  unfold Safety, σ, GC_traceT_traceS, induced_connection, up_rel; simpl. *)
(*   intros π Hsafety t__s Ht. *)
(*   rewrite not_forall_ex_not in Ht; *)
(*     setoid_rewrite not_imp in Ht. *)
(*   destruct Ht as [t__t [Hrel Hnπ]]. *)
(*   destruct (Hsafety t__t Hnπ) as [m__t [Hm1 Hm2]]. *)
(*   exists (finpref_TS m__t). *)
(*   split. *)
(*   - destruct Hrel as [Hrel | Hrel]. *)
(*     + inversion Hrel; subst. *)
(*       * destruct m__t as [l' [e' | []] | l']; *)
(*           try now inversion Hm1 as [Hm1' ?]; inversion Hm1'; subst. *)
(*         now assumption. *)
(*       * destruct m__t as [l' [e' | []] | l']; *)
(*           try now auto. *)
(*       * destruct m__t as [l' [e' | []] | l']; *)
(*           try now auto. *)
(*     + destruct Hrel as [m [H1 H2]]; subst. *)
(*       destruct m__t as [l' [e' | []] | l']; *)
(*         try now auto. *)
(*       * now inversion Hm1 as [Hm1' ?]; inversion Hm1'. *)
(*       * inversion Hm1 as [Hm1' ?]; inversion Hm1'; subst. *)
(*         now destruct t__s as [l'' e'' | l'' | s'']; *)
(*           assumption. *)
(*       * destruct t__s as [l'' e'' | l'' | s'']; *)
(*           try now eapply Stream.list_list_prefix_trans; eassumption. *)
(*         simpl in *. *)
(*         (* TODO: same proof as above, factorize *) *)
(*         { clear -H2 Hm1. *)
(*           generalize dependent s''. generalize dependent m. *)
(*           rename l' into l. *)
(*           induction l as [| e l]; intros m Hlm s Hms. *)
(*           - reflexivity. *)
(*           - destruct m as [| e' l']; *)
(*               destruct Hlm; *)
(*               subst. *)
(*             destruct s as [e s]. *)
(*             simpl in *. *)
(*             destruct Hms as [? Hl's]; subst. *)
(*             split; first reflexivity. *)
(*             now eapply IHl; eassumption. *)
(*         } *)
(*   - intros t__s' Hpref'. *)
(*     rewrite not_forall_ex_not; *)
(*       setoid_rewrite not_imp. *)
(*     exists (trace_ST t__s'). *)
(*     split. *)
(*     + destruct t__s' as [l e | l | s]. *)
(*       * left. now constructor. *)
(*       * left. now constructor. *)
(*       * left. now constructor. *)
(*     + destruct m__t as [l [e | []] | l]. *)
(*       * destruct t__s' as [l' e' | l' | s']; *)
(*           try now auto. *)
(*         apply Hm2. *)
(*         now destruct Hpref'; subst. *)
(*       * destruct Hrel as [Hrel | Hrel]. *)
(*         -- destruct Hrel; try now auto. *)
(*            inversion Hm1 as [Hm1' _]; inversion Hm1'. *)
(*         -- destruct Hrel as [m [H1 H2]]; *)
(*              subst. *)
(*            apply Hm2. *)
(*            destruct t__s' as [l' e' | l' | s']; *)
(*              try now auto. *)
(*            ++ simpl in *. admit. (* wrong? *) *)
(*            ++ admit. *)
(*            ++ simpl in *. admit. *)
(*       * destruct t__s' as [l' e' | l' | s']; *)
(*           try now auto. *)
(* Admitted. *)
