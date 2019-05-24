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
| syntactic_eq_tstop : forall l es,
    syntactic_eq (tstop l es) (tstop l (inl es))
| syntactic_eq_tsilent : forall l,
    syntactic_eq (tsilent _ l) (tsilent _ l)
| syntactic_eq_tstream : forall s,
    syntactic_eq (tstream _ s) (tstream _ s)
.
Notation "t__s '≡' t__t" := (syntactic_eq t__s t__t) (no associativity, at level 10).
Hint Constructors syntactic_eq.

Axiom prefixTS : finprefT -> traceS -> Prop.

Definition rel : traceS -> traceT -> Prop :=
  fun t__s t__t => t__s ≡ t__t \/ exists m, (t__t = tstop m OOM /\ prefixTS (ftbd _ m) t__s).
Hint Unfold rel.

Inductive syntactic_eq_finpref : finprefS -> finprefT -> Prop :=
| syntactic_eq_fstop : forall l es,
    syntactic_eq_finpref (fstop l es) (fstop l (inl es))
| syntactic_eq_ftbd : forall l,
    syntactic_eq_finpref (ftbd _ l) (ftbd _ l)
.

Definition rel_finpref : finprefS -> finprefT -> Prop :=
  fun m__s m__t => syntactic_eq_finpref m__s m__t \/ exists l, (m__t = fstop l OOM /\ prefix_finpref (ftbd _ l) m__s).

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
  - exists (tstop l (an_es is_endstate)). split.
    apply HDense. econstructor; eexists; eauto.
    right; eexists; split; eauto.
    admit. (* property of prefixTS *)
  - destruct Hfin as [l' [e' Hn]].
    inversion Hn.
  - destruct Hfin as [l' [e' Hn]].
    inversion Hn.
Admitted.

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
  | tstop l (inr _) => tsilent _ l
  | tsilent l => tsilent _ l
  | tstream s => tstream _ s
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
    admit. (* trivial property of prefixTS *)
Admitted.

Definition finpref_ST (m__s : finprefS) : finprefT :=
  match m__s with
  | fstop l e => fstop l (inl e)
  | ftbd l => ftbd _ l
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
           admit. (* trivial property of prefixTS *)
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
Admitted.

Definition finpref_TS (m__t : finprefT) : finprefS :=
  match m__t with
  | fstop l (inl e) => fstop l e
  | fstop l (inr e) => ftbd _ l
  | ftbd l => ftbd _ l
  end.

Definition trace_ST (t__s : traceS) : traceT :=
  match t__s with
  | tstop l e => tstop l (inl e)
  | tsilent l => tsilent _ l
  | tstream s => tstream _ s
  end.

Lemma σ_preserves_safety : forall (π : propT),
    Safety π -> Safety (σ π).
Proof.
  unfold Safety, σ, GC_traceT_traceS, induced_connection, up_rel; simpl.
  intros π Hsafety t__s Ht.
  rewrite not_forall_ex_not in Ht;
    setoid_rewrite not_imp in Ht.
  destruct Ht as [t__t [Hrel Hnπ]].
  destruct (Hsafety t__t Hnπ) as [m__t [Hm1 Hm2]].
  exists (finpref_TS m__t).
  split.
  - destruct Hrel as [Hrel | Hrel].
    + inversion Hrel; subst.
      * destruct m__t as [l' [e' | []] | l'];
          try now inversion Hm1 as [Hm1' ?]; inversion Hm1'; subst.
        now assumption.
      * destruct m__t as [l' [e' | []] | l'];
          try now auto.
      * destruct m__t as [l' [e' | []] | l'];
          try now auto.
    + destruct Hrel as [m [H1 H2]]; subst.
      destruct m__t as [l' [e' | []] | l'];
        try now auto.
      * now inversion Hm1 as [Hm1' ?]; inversion Hm1'.
      * inversion Hm1 as [Hm1' ?]; inversion Hm1'; subst.
        destruct t__s as [l'' e'' | l'' | s''].
        -- admit. (* trivial from H2 *)
        -- simpl. admit. (* trivial from H2 *)
        -- simpl. admit. (* trivial from H2 *)
      * destruct t__s as [l'' e'' | l'' | s''].
        -- simpl. admit. (* trivial from Hm1 and H2 *)
        -- simpl. admit. (* trivial from Hm1 and H2 *)
        -- simpl. admit. (* trivial from Hm1 and H2 *)
  - intros t__s' Hpref'.
    rewrite not_forall_ex_not;
      setoid_rewrite not_imp.
    exists (trace_ST t__s').
    split.
    + destruct t__s' as [l e | l | s].
      * left. now constructor.
      * left. now constructor.
      * left. now constructor.
    + apply Hm2.
      destruct m__t as [l [e | []] | l].
      * destruct t__s' as [l' e' | l' | s'];
          try now auto.
        now destruct Hpref'; subst.
      * admit. (* NOT trivial *)
      * destruct t__s' as [l' e' | l' | s'];
          try now auto.
Admitted.
