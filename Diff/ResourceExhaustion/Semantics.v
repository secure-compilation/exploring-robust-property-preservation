Require Import Coq.Program.Equality.
Require Import Maps Imp.
Require Import Sequences.
Require Import List.
Import ListNotations.

(** In this chapter: various styles of semantics for the Imp language
  from "Software Foundations", and equivalence results between these
  semantics. *)

(** * 2. Small-step semantics.  *)

(** An important property of this reduction relation is that it is functional,
  in the sense that a given configuration can reduce to at most one configuration. *)

Lemma cstep_functional_states :
  forall cs cs1 e1, cstep cs e1 cs1 -> forall cs2 e2, cstep cs e2 cs2 -> cs1 = cs2.
Proof.
  induction 1; intros cs2 e2 Hstep; inversion Hstep; subst;
    try reflexivity;
    try congruence.
  - generalize (IHcstep _ _ H5). congruence.
  - inversion H.
  - inversion H4.
Qed.

Lemma cstep_functional_event :
  forall cs cs1 e1, cstep cs e1 cs1 ->
               forall cs2 e2, cstep cs e2 cs2 -> e1 = e2.
Proof.
  induction 1; intros cs2 e2 Hstep; inversion Hstep; subst;
    try reflexivity;
    try congruence.
  - generalize (IHcstep _ _ H5). congruence.
  - inversion H.
  - inversion H4.
Qed.

(** In small-step style, the semantics of a command [c] in a state [st]
  is determined by forming sequences of reductions starting from [c, st].
- Finite sequences: zero, one or several reductions (reflexive transitive closure)
- Infinite sequences: infinitely many reductions.

These sequences are defined using the generic [star] and [infseq] operators
over binary relations, which are defined in module [Sequences], along
with useful lemmas. *)

Definition terminates (c: com) (st: state) (st': state)
           (l : list (TraceModel.ev event)) : Prop :=
  star_tr cstep (c, st) l (SKIP, st').

Definition diverges (c: com) (st: state)
           (s : @Stream.stream (TraceModel.ev event)) : Prop :=
  infseq_tr cstep s (c, st).

(** *** Exercise (2 stars, optional) *)
(** Show that the final state of a terminating program is unique,
  and that a program cannot both terminate and diverge.
  Hint: use the generic determinism properties found at the end of module [Sequence],
  plus the following useful remark. *)

Remark irred_SKIP:
  forall st, irred_tr cstep (SKIP, st).
Proof.
  unfold irred_tr; intros st st' STEP.
  (* FILL IN HERE *)
Admitted.

Lemma terminates_unique:
  forall c st st1 st2 l1 l2,
    terminates c st st1 l1 ->
    terminates c st st2 l2 -> st1 = st2 /\ l1 = l2.
Proof.
  unfold terminates; intros. 
  (* FILL IN HERE *)
Admitted.

Lemma terminates_diverges_exclusive:
  forall c st st' l s, terminates c st st' l -> diverges c st s -> False.
Proof.
  (* FILL IN HERE *)
Admitted.

(** *** Exercise (3 stars, recommended) *)
(** Show that Imp programs cannot go wrong.  Hint: first prove the following
  "progress" result for non-[SKIP] commands. *)

Lemma cstep_progress:
  forall c st, c = SKIP \/ exists c', exists st', exists e, c / st ==> c' / st' ! e.
Proof.
  induction c; intros.
  (* FILL IN HERE *)
Admitted.

Definition goes_wrong (c: com) (st: state) : Prop :=
  exists c', exists st', exists l,
  star_tr cstep (c, st) l (c', st') /\ irred_tr cstep (c', st') /\ c' <> SKIP.

Lemma not_goes_wrong:
  forall c st, ~(goes_wrong c st).
Proof.
  unfold not, goes_wrong, irred_tr; intros.
  (* FILL IN HERE *)
Admitted.

(** As a corollary, using the [infseq_or_finseq] theorem from module [Sequence], we obtain that any IMP program either terminates safely or diverges. *)

Lemma terminates_or_diverges:
  forall c st, (exists st', exists l, terminates c st st' l) \/ (exists s, diverges c st s).
Proof.
  (* FILL IN HERE *)
Admitted.

(** Sequences of reductions can go under a sequence context, generalizing
  rule [CS_SeqStep]. *)

Lemma star_CS_SeqStep:
  forall c2 st c st' c' l,
    star_tr cstep (c, st) l (c', st') ->
    star_tr cstep ((c;;c2), st) l ((c';;c2), st').
Proof.
  intros. dependent induction H.
- apply star_tr_refl.
- destruct b as [c1 st1].
  apply star_tr_step with (c1;;c2, st1). apply CS_SeqStep. auto. auto.  
Qed.

(** We now recall the equivalence result between 
- termination according to the big-step semantics
- existence of a finite sequence of reductions to [SKIP]
  according to the small-step semantics.

We start with the implication big-step ==> small-step, which is
a straightforward induction on the big-step evaluation derivation. *)

Theorem ceval_to_csteps:
  forall c st st' l,
  c / st \\ st' --> l -> star_tr cstep (c, st) l (SKIP, st').
Proof.
  induction 1.
- (* SKIP *)
  apply star_tr_refl.
- (* x := a1 *)
  apply star_tr_one. apply CS_Ass. auto.
- (* sequence *)
  eapply star_tr_trans. apply star_CS_SeqStep. apply IHceval1.
  replace l' with ([] ++ l' ).
  eapply star_tr_step. apply CS_SeqFinish. auto.
  reflexivity.
- (* if true *)
  replace l with ([] ++ l).
  eapply star_tr_step. apply CS_IfTrue. auto. auto.
  reflexivity.
- (* if false *)
  replace l with ([] ++ l).
  eapply star_tr_step. apply CS_IfFalse. auto. auto.
  reflexivity.
- (* while stop *)
  replace [] with ([] ++ [] : list (TraceModel.ev event)).
  eapply star_tr_step. apply CS_While. 
  apply star_tr_one. apply CS_IfFalse. auto.
  reflexivity.
- (* while loop *)
  replace (l ++ l') with ([] ++ (l ++ l')).
  eapply star_tr_step. apply CS_While.
  replace (l ++ l') with ([] ++ (l ++ l')).
  eapply star_tr_step. apply CS_IfTrue. auto.
  eapply star_tr_trans. apply star_CS_SeqStep. apply IHceval1. 
  replace l' with ([] ++ l').
  eapply star_tr_step. apply CS_SeqFinish. auto.
  reflexivity. reflexivity. reflexivity.
- (* output *)
  apply star_tr_one. apply CS_Output. auto.
Qed.

(** The reverse implication, from small-step to big-step, is more subtle.
The key lemma is the following, showing that one step of reduction
followed by a big-step evaluation to a final state can be collapsed
into a single big-step evaluation to that final state. *)


Lemma cstep_append_ceval:
  forall c1 st1 c2 st2 l l',
    c1 / st1 ==> c2 / st2 ! l ->
    forall st3,
      c2 / st2 \\ st3 --> l' ->
      c1 / st1 \\ st3 --> (l ++ l').
Proof.
  intros until l'; intros STEP. generalize dependent l'.
  dependent induction STEP; intros.
- (* CS_Ass *)
  inversion H; subst. simpl. apply E_Ass. auto.
- (* CS_SeqStep *)
  inversion H; subst.
  replace (e ++ l ++ l'0) with ((e ++ l) ++ l'0). apply E_Seq with st'.
  eauto. auto.
  now rewrite app_assoc.
- (* CS_SeqFinish *)
  eapply E_Seq. apply E_Skip. assumption.
- (* CS_IfTrue *)
  apply E_IfTrue; auto.
- (* CS_IfFalse *)
  apply E_IfFalse; auto.
- (* CS_While *)
  inversion H; subst. 
  + (* while loop *)
    inversion H7; subst.
    replace ([] ++ l ++ l'0) with (([] ++ l) ++ l'0).
    apply E_WhileTrue with st'; auto.
    reflexivity.
  + (* while stop *)
    inversion H7; subst. 
    apply E_WhileFalse; auto.
- inversion H; subst.
  now eapply E_Output.
Qed.


(** As a consequence, a term that reduces to [SKIP] evaluates in big-step
  with the same final state. *)

Theorem csteps_to_ceval:
  forall st c st' l,
  star_tr cstep (c, st) l (SKIP, st') -> c / st \\ st' --> l.
Proof.
  intros. dependent induction H.
- apply E_Skip.
- destruct b as [c1 st1]. apply cstep_append_ceval with c1 st1; auto.
Qed.

(** * 3. Small-step semantics with continuations. *)

(** We now introduce an alternate form of the small-step semantics above
  where the command to be reduced is explicitly decomposed into:
- a sub-command under focus, where computation takes place;
- a continuation (or context) describing the position of this sub-command
  in the whole command, or, equivalently, describing the parts of the
  whole command that remain to be reduced once the sub-command is done.

As a consequence, the small-step semantics is presented as a transition relation
between triples (subcommand-under-focus, continuation, state).
Previously, we had transitions between pairs (whole-command, state).

The syntax of continuations is as follows:
*)

Inductive cont : Type :=
  | Kstop : cont
  | Kseq : com -> cont -> cont
  | Kwhile : bexp -> com -> cont -> cont.

(** Intuitive meaning of these constructors:
- [Kstop] means that, after the sub-command under focus terminates, nothing remains to
  be done, and execution can stop.  In other words, the sub-command under
  focus is the whole command.
- [Kseq c k] means that, after the sub-command terminates, we still need
  to execute command [c] in sequence, then continue as described by [k].
- [Kwhile b c k] means that, after the sub-command terminates, we still need
  to execute a loop [WHILE b DO c END], then continue as described by [k].
*)

(** Another way to forge intuitions about continuations is to ponder the following
  [apply_cont k c] function, which takes a sub-command [c] under focus
  and a continuation [k], and rebuilds the whole command.  It simply
  puts [c] in lefmost position in a nest of sequences as described by [k].
*)

Fixpoint apply_cont (k: cont) (c: com) : com :=
  match k with
  | Kstop => c
  | Kseq c1 k1 => apply_cont k1 (c ;; c1)
  | Kwhile b1 c1 k1 => apply_cont k1 (c ;; WHILE b1 DO c1 END)
  end.

(** Transitions between (subcommand-under-focus, continuation, state) triples
  perform conceptually different kinds of actions:
- Computation: evaluate an arithmetic expression or boolean expression
  and modify the triple according to the result of the evaluation.
- Focusing: replace the sub-command by a sub-sub-command that is to be
  evaluated next, possibly enriching the continuation as a consequence.
- Resumption: when the sub-command is [SKIP] and therefore fully executed,
  look at the head of the continuation to see what to do next.

Here are the transition rules, classified by the kinds of actions they implement.
*)

Inductive kstep : (com * cont * state) -> list (TraceModel.ev event) -> (com * cont * state) -> Prop :=

  | KS_Ass : forall st i a k n,            (**r Computation for assignments *)
      aeval st a = n ->
      kstep ((i ::= a), k, st) [] (SKIP, k, t_update st i n)

  | KS_Seq : forall st c1 c2 k,  (**r Focusing on the left part of a sequence *)
      kstep ((c1 ;; c2), k, st) [] (c1, Kseq c2 k, st)

  | KS_IfTrue : forall st b c1 c2 k,  (**r Computation for conditionals *)
      beval st b = true ->
      kstep (IFB b THEN c1 ELSE c2 FI, k, st) [] (c1, k, st)
  | KS_IfFalse : forall st b c1 c2 k,
      beval st b = false ->
      kstep (IFB b THEN c1 ELSE c2 FI, k, st) [] (c2, k, st)

  | KS_WhileTrue : forall st b c k,  (**r Computation and focusing for loops *)
      beval st b = true ->
      kstep (WHILE b DO c END, k, st) [] (c, Kwhile b c k, st)
  | KS_WhileFalse : forall st b c k,
      beval st b = false ->
      kstep (WHILE b DO c END, k, st) [] (SKIP, k, st)

  | KS_SkipSeq: forall c k st,  (**r Resumption on [SKIP] *)
      kstep (SKIP, Kseq c k, st) [] (c, k, st)
  | KS_SkipWhile: forall b c k st,
      kstep (SKIP, Kwhile b c k, st) [] (WHILE b DO c END, k, st)

  | KS_Out : forall st a k n, (**r Computation for outputs *)
      aeval st a = n ->
      kstep (OUT a, k, st) [n] (SKIP, k, st).

(** Note: the [kstep] relation is not inductive, in the sense that the premises
  of the rules never involve the [kstep] relation itself.  Contrast with
  the [cstep] relation, which is recursive in the [CS_SeqStep] case:
<<
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ==> c1' / st' ->
      (c1 ; c2) / st ==> (c1' ; c2) / st'
>>
  For [cstep], this rule enables us to reduce "deep" within a sequence.
  In contrast, [kstep] always reduce at the top of the given [(c,k,st)] triple.
  Reducting within a sequence is achieved by first focusing on the left
  part of the sequence (rule [KS_Seq]), bringing it to the top of the triple,
  then working on this left part.
*)

(** As in section 2, we can define the behavior of a command in terms of
  sequences of [kstep] reductions.  
  Initial configurations are of the form (whole-command, [Kstop], initial-state).
  Final configurations are ([SKIP], [Kstop], final-state).  *)

Definition kterminates (c: com) (st: state) (st': state) l : Prop :=
  star_tr kstep (c, Kstop, st) l (SKIP, Kstop, st').

Definition kdiverges (c: com) (st: state) s : Prop :=
  infseq_tr kstep s (c, Kstop, st) .

Definition ksilent (c : com) (st : state) (st' : state) l : Prop :=
  exists c' k', star_tr kstep (c, Kstop, st) l (c', k', st') /\
            infseq_silent kstep (c', k', st').

(** ** Extensions to other control structures *)

(** A remarkable feature of continuation semantics is that they extend very easily
  to other control structures besides "if-then-else" and "while" loops.
  Consider for instance the "break" construct of C, C++ and Java, which
  immediately terminates the nearest enclosing "while" loop.  Assume we
  extend the type of commands with a [BREAK] constructor.  Then, all we need
  to give "break" a semantics is to add two resumption rules:
<<
  | KS_BreakSeq: forall c k st,
      kstep (BREAK, Kseq c k, st) (BREAK, k, st)
  | KS_BreakWhile: forall b c k st,
      kstep (BREAK, Kwhile b c k, st) (SKIP, k, st)
>>
  The first rule says that a [BREAK] statement "floats up" pending sequences,
  skipping over the computations they contain.  Eventually, a [Kwhile]
  continuation is encountered, meaning that the [BREAK] found its enclosing
  loop.  Then, the second rule discards the [Kwhile] continuation and
  turns the [BREAK] into a [SKIP], effectively terminating the loop.
  That's all there is to it!
**)

(** If you're curious about adding "break" to the big-step semantics of
  section 1, see exercise [BreakImp] in the [Imp] module of 
  Software Foundations. *)

(** *** Exercise (2 star_trs, recommended) *)
(** Besides "break", C, C++ and Java also have a "continue" statement
  that terminates the current iteration of the enclosing loop,
  then resumes the loop at its next iteration (instead of stopping
  the loop like "break" does). Give the transition rules
  for the "continue" statement. *)

(** *** Exercise (3 star_trs, optional) *)
(** In Java, loops as well as "break" and "continue" statements carry
  an optional label.  "break" without a label exits out of the immediately
  enclosing loop, but "break lbl" exits out of the first enclosing loop
  that carries the label "lbl".  Similarly for "continue".
  Give the transition rules for "break lbl" and "continue lbl". *)

(** ** Relating the continuation semantics with the other semantics *)

(** As in section 2, we show that termination according to the continuation semantics
  (predicate [kterminates]) is equivalent to big-step evaluation.
  The first implication, from big-step evaluation to termination, is a
  straightforward induction on the structure of the big-step
  evaluation derivation. *)

Theorem ceval_to_ksteps:
  forall c st st' l,
  c / st \\ st' --> l ->
  forall k, star_tr kstep (c, k, st) l (SKIP, k, st').
Proof.
  induction 1; intros.
- (* SKIP *)
  apply star_tr_refl.
- (* x := a1 *)
  apply star_tr_one. apply KS_Ass. auto.
- (* sequence *)
  replace (l ++ l') with ([] ++ l ++ l').
  eapply star_tr_step. apply KS_Seq. 
  eapply star_tr_trans. apply IHceval1.
  replace l' with ([] ++ l').
  eapply star_tr_step. apply KS_SkipSeq. 
  apply IHceval2.
  reflexivity. reflexivity.
- (* if true *)
  replace l with ([] ++ l).
  eapply star_tr_step. apply KS_IfTrue. auto. auto.
  reflexivity.
- (* if false *)
  replace l with ([] ++ l).
  eapply star_tr_step. apply KS_IfFalse. auto. auto.
  reflexivity.
- (* while stop *)
  apply star_tr_one. apply KS_WhileFalse. auto.
- (* while loop *)
  replace (l ++ l') with ([] ++ (l ++ l')).
  eapply star_tr_step. apply KS_WhileTrue. auto. 
  eapply star_tr_trans. apply IHceval1.
  replace l' with ([] ++ l').
  eapply star_tr_step. apply KS_SkipWhile. 
  apply IHceval2.
  reflexivity. reflexivity.
- (* output *)
  replace [n] with ([n] ++ []).
  eapply star_tr_step. apply KS_Out.
  assumption.
  apply star_tr_refl.
  reflexivity.
Qed.

(** For the reverse implication, we adapt lemma [cstep_append_ceval] to show
  that one step of reduction [kstep (c1, k1, st1) (c2, k2, st2)] 
  followed by big-step evaluation of [(c2, k2, st2)] is equivalent to
  big-step evaluation of [(c1, k1, st1)].  However, we now need to define
  big-step evaluation of a pair [(c, k)] of a subcommand and a continuation.
  We define this notion as first evaluating [c], obtaining a modified state,
  then performing the latent computations described by [k], obtaining the final
  state. *)

Inductive keval : cont -> state -> state -> list (TraceModel.ev event) -> Prop :=
  | KE_stop: forall st,
      keval Kstop st st nil
  | KE_seq: forall c k st1 st2 st3 l l',
      ceval c st1 st2 l -> keval k st2 st3 l' ->
      keval (Kseq c k) st1 st3 (l ++ l') 
  | KE_while: forall b c k st1 st2 st3 l l',
      ceval (WHILE b DO c END) st1 st2 l -> keval k st2 st3 l' ->
      keval (Kwhile b c k) st1 st3 (l ++ l').


Inductive ckeval: com -> cont -> state -> state -> list (TraceModel.ev event) -> Prop :=
  | CKE_intro: forall c k st1 st2 st3 l l',
      ceval c st1 st2 l -> keval k st2 st3 l' ->
      ckeval c k st1 st3 (l ++ l').

Lemma kstep_append_ckeval :
  forall c1 k1 st1 c2 k2 st2 l,
    kstep (c1, k1, st1) l (c2, k2, st2) ->
    forall st3 l',
      ckeval c2 k2 st2 st3 l' ->
      ckeval c1 k1 st1 st3 (l ++ l').
Proof.
  intros until l. intro STEP. dependent induction STEP; intros; simpl.
- (* KS_Ass *)
  inversion H; subst. inversion H0; subst. econstructor. apply E_Ass. reflexivity. auto.
- (* KS_Seq *)
  inversion H; subst. inversion H1; subst.
  replace (l ++ l0 ++ l') with ((l ++ l0) ++ l').
  econstructor.
  eapply E_Seq; eauto. auto.
  simpl. now apply app_assoc_reverse.
- (* KS_IfTrue *)
  inversion H0; subst.
  replace ([] ++ l ++ l'0) with (l ++ l'0).
  econstructor.
  apply E_IfTrue; eauto. auto.
  reflexivity.
- (* KS_IfFalse *)
  inversion H0; subst. simpl. econstructor. apply E_IfFalse; eauto. auto.
- (* KS_WhileTrue *)
  inversion H0; subst. inversion H2; subst.
  replace (l ++ l0 ++ l') with ((l ++ l0) ++ l').
  econstructor. eapply E_WhileTrue; eauto. auto.
  apply app_assoc_reverse.
- (* KS_WhileFalse *)
  inversion H0; subst. inversion H1; subst. econstructor. apply E_WhileFalse; auto. auto. 
- (* KS_SkipSeq *)
  inversion H; subst.
  replace (l ++ l'0) with ([] ++ (l ++ l'0)). econstructor. apply E_Skip. eapply KE_seq; eauto.
  reflexivity.
- (* KS_SkipWhile *)
  inversion H; subst.
  replace (l ++ l'0) with ([] ++ (l ++ l'0)).
  econstructor. apply E_Skip. eapply KE_while; eauto.
  reflexivity.
- inversion H; subst.
  inversion H0; subst.
  simpl in *.
  replace (aeval st0 a :: l'0) with ([aeval st0 a] ++ l'0).
  econstructor.
  now constructor.
  assumption.
  reflexivity.
Qed.

(** We can, then, extend this result to sequences of [kstep] transitions, 
  and conclude. *)
Lemma ksteps_append_ckeval:
  forall c1 k1 st1 c2 k2 st2 st3 l l',
  star_tr kstep (c1, k1, st1) l (c2, k2, st2) ->
  ckeval c2 k2 st2 st3 l' ->
  ckeval c1 k1 st1 st3 (l ++ l').
Proof.
  intros. dependent induction H.
- auto. 
- destruct b as [[c' k'] st'].
  replace ((l1 ++ l2) ++ l') with (l1 ++ l2 ++ l').
  eapply kstep_append_ckeval; eauto.
  now apply app_assoc.
Qed.

Theorem kterminates_to_ceval:
  forall c st st' l,
  kterminates c st st' l -> c / st \\ st' --> l.
Proof.
  unfold kterminates; intros. 
  assert (CKEV: ckeval c Kstop st st' l).
  { replace l with (l ++ []).
    eapply ksteps_append_ckeval; eauto.
    replace ([] : list (TraceModel.ev event)) with ([] ++ [] : list (TraceModel.ev event)).

    econstructor. apply E_Skip. apply KE_stop.
  reflexivity. apply app_nil_r. }
  inversion CKEV; subst. inversion H1; subst. rewrite app_nil_r. auto.
Qed.

(** From the theorems above, it follows that the two small-step semantics
  capture the same notion of termination. *)

Theorem kterminates_iff_terminates:
  forall c st st' l, kterminates c st st' l <-> terminates c st st' l.
Proof.
  intros; split; intros.
- apply ceval_to_csteps. apply kterminates_to_ceval. auto.
- apply ceval_to_ksteps. apply csteps_to_ceval. auto.
Qed.

(** For additional confidence, we can show that the two small-step semantics
  (with and without continuations) capture the same notion of divergence.
  The proof is surprisingly involved and consists in relating infinite
  sequences of [kstep] transitions from an initial state [(c, k, st)]
  with infinite sequences of [cstep] transitions from the corresponding
  initial state [(apply_cont k c, st)].  The proofs are included below
  for completeness, but can be skipped on first reading. *)

Remark cstep_apply_cont:
  forall k c1 st1 c2 st2 e,
  cstep (c1, st1) e (c2, st2) ->
  cstep (apply_cont k c1, st1) e (apply_cont k c2, st2).
Proof.
  induction k; intros; simpl.
- auto.
- apply IHk. apply CS_SeqStep. auto.
- apply IHk. apply CS_SeqStep. auto.
Qed.

(* Lemma kinfseq_cinfseq: *)
(*   forall c k st, *)
(*   infseq kstep (c, k, st) -> *)
(*   exists c', exists k', exists st', *)
(*   plus cstep (apply_cont k c, st) (apply_cont k' c', st') *)
(*   /\ infseq kstep (c', k', st'). *)
(* Proof. *)
(*   induction c; intros; inversion H; clear H; subst. *)
(* - (* skip *) *)
(*   inversion H0; clear H0; subst. *)
(* + (* skip seq *) *)
(*   do 3 econstructor; split. simpl. apply plus_one. apply cstep_apply_cont. apply CS_SeqFinish. auto. *)
(* + (* skip while *) *)
(*   do 3 econstructor; split. simpl. apply plus_one. apply cstep_apply_cont. apply CS_SeqFinish. auto. *)
(* - (* assign *) *)
(*   inversion H0; clear H0; subst. *)
(*   do 3 econstructor; split. apply plus_one. apply cstep_apply_cont. apply CS_Ass. reflexivity. auto. *)
(* - (* seq *) *)
(*   inversion H0; clear H0; subst. *)
(*   change (apply_cont k (c1;;c2)) with (apply_cont (Kseq c2 k) c1).  *)
(*   eapply IHc1; eauto.  *)
(* - (* if *) *)
(*   inversion H0; clear H0; subst. *)
(* + (* if true *)  *)
(*   do 3 econstructor; split. apply plus_one. apply cstep_apply_cont. apply CS_IfTrue; auto. auto. *)
(* + (* if false *)  *)
(*   do 3 econstructor; split. apply plus_one. apply cstep_apply_cont. apply CS_IfFalse; auto. auto. *)
(* - (* while *) *)
(*   inversion H0; clear H0; subst. *)
(* + (* while true *) *)
(*   exists c; exists (Kwhile b c k); exists st; split. *)
(*   simpl. eapply plus_left. apply cstep_apply_cont. apply CS_While.  *)
(*   apply star_tr_one. apply cstep_apply_cont. apply CS_IfTrue; auto.  *)
(*   auto. *)
(* + (* while false *) *)
(*   do 3 econstructor; split. *)
(*   eapply plus_left. apply cstep_apply_cont. apply CS_While. *)
(*   apply star_tr_one. apply cstep_apply_cont. apply CS_IfFalse; auto. *)
(*   auto. *)
(* Qed. *)

(* (** We now prepare for the reverse diagram: decomposing infinite sequences of *)
(*   [cstep] transitions in terms of [kstep] transitions.  First, a technical *)
(*   inversion lemma on [cstep] reductions over commands of the form [apply_cont k c]. *) *)

(* Inductive cstep_apply_cont_cases: cont -> com -> state -> com -> state -> Prop := *)
(*   | cacc_base: forall c1 st1 c2 st2 k, *)
(*       cstep (c1, st1) (c2, st2) -> *)
(*       cstep_apply_cont_cases k c1 st1 (apply_cont k c2) st2 *)
(*   | cacc_skip_seq: forall c k st, *)
(*       cstep_apply_cont_cases (Kseq c k) SKIP st (apply_cont k c) st *)
(*   | cacc_skip_while: forall b c k st, *)
(*       cstep_apply_cont_cases (Kwhile b c k) SKIP st (apply_cont k (WHILE b DO c END)) st. *)

(* Lemma invert_cstep_apply_cont: *)
(*   forall k c st c' st', *)
(*   cstep (apply_cont k c, st) (c', st') -> *)
(*   cstep_apply_cont_cases k c st c' st'. *)
(* Proof. *)
(*   induction k; simpl; intros.  *)
(* - (* Kstop *) *)
(*   change c' with (apply_cont Kstop c'). apply cacc_base; auto. *)
(* - (* Kseq *) *)
(*   specialize (IHk _ _ _ _ H). inversion IHk; subst. *)
(*   + (* base *) *)
(*     inversion H0; clear H0; subst. *)
(*     * (* seq step *) *)
(*       change (apply_cont k (c1';;c)) with (apply_cont (Kseq c k) c1').  *)
(*       apply cacc_base; auto. *)
(*     * (* seq finish *) *)
(*       apply cacc_skip_seq. *)
(* - (* Kwhile *) *)
(*   specialize (IHk _ _ _ _ H). inversion IHk; subst. *)
(*   + (* base *) *)
(*     inversion H0; clear H0; subst. *)
(*     * (* seq step *) *)
(*       change (apply_cont k (c1';;WHILE b DO c END)) with (apply_cont (Kwhile b c k) c1').  *)
(*       apply cacc_base; auto. *)
(*     * (* seq finish *) *)
(*       apply cacc_skip_while. *)
(* Qed. *)

(* Lemma cinfseq_kinfseq: *)
(*   forall c k st, *)
(*   infseq cstep (apply_cont k c, st) -> *)
(*   exists c', exists k', exists st', *)
(*   plus kstep (c, k, st) (c', k', st') *)
(*   /\ infseq cstep (apply_cont k' c', st'). *)
(* Proof. *)
(*   intros. inversion H; clear H; subst. destruct b as [c' st']. *)
(*   specialize (invert_cstep_apply_cont _ _ _ _ _ H0). intros CASES; inversion CASES; subst. *)
(* - (* base *) *)
(*   clear H0 CASES. revert k H1. dependent induction H; intros. *)
(*   + (* assign *) *)
(*     do 3 econstructor; split. apply plus_one. apply KS_Ass. reflexivity. auto. *)
(*   + (* seq step *) *)
(*     destruct (IHcstep _ _ _ _ eq_refl eq_refl (Kseq c0 k) H1) *)
(*     as [c'' [k'' [st'' [A B]]]]. *)
(*     exists c''; exists k''; exists st''; split; auto. *)
(*     eapply plus_left. apply KS_Seq. apply plus_star_tr. auto.  *)
(*   + (* seq finish *) *)
(*     do 3 econstructor; split. *)
(*     eapply plus_left. apply KS_Seq. apply star_tr_one. apply KS_SkipSeq.  *)
(*     auto. *)
(*   + (* if true *) *)
(*     do 3 econstructor; split. apply plus_one. apply KS_IfTrue. auto. auto. *)
(*   + (* if false *) *)
(*     do 3 econstructor; split. apply plus_one. apply KS_IfFalse. auto. auto. *)
(*   + (* while *) *)
(*     inversion H1; clear H1; subst. destruct b0 as [c'' st''].  *)
(*     specialize (invert_cstep_apply_cont _ _ _ _ _ H). intros CASES; inversion CASES; clear CASES; subst. *)
(*     inversion H1; clear H1; subst. *)
(*     * (* while true *) *)
(*       do 3 econstructor; split. apply plus_one. apply KS_WhileTrue. auto. auto. *)
(*     * (* while false *) *)
(*       do 3 econstructor; split. apply plus_one. apply KS_WhileFalse. auto. auto. *)
(* - (* skip seq *) *)
(*   do 3 econstructor; split. apply plus_one. apply KS_SkipSeq. auto. *)
(* - (* skip while *) *)
(*   do 3 econstructor; split. apply plus_one. apply KS_SkipWhile. auto. *)
(* Qed. *)

(* (** The desired equivalence between the two notions of divergence then follows *)
(*   from the coinduction principles given in module [Sequence]. *) *)

(* Theorem kdiverges_iff_diverges: *)
(*   forall c st, kdiverges c st <-> diverges c st. *)
(* Proof. *)
(*   intros; split; intros. *)
(* - (* kdiverges -> diverges *) *)
(*   unfold diverges.  *)
(*   apply infseq_coinduction_principle_2 with *)
(*     (X := fun c_st => exists c, exists k, exists st, *)
(*                       c_st = (apply_cont k c, st) /\ infseq kstep (c, k, st)). *)
(*   intros. destruct H0 as [c1 [k1 [st1 [EQ ISEQ]]]]. *)
(*   destruct (kinfseq_cinfseq _ _ _ ISEQ) as [c2 [k2 [st2 [CSTEPS ISEQ']]]].  *)
(*   exists (apply_cont k2 c2, st2); split. *)
(*   subst a; auto. *)
(*   exists c2; exists k2; exists st2; auto. *)
(*   exists c; exists Kstop; exists st; auto. *)
(* - (* diverges -> kdiverges *) *)
(*   unfold kdiverges.  *)
(*   apply infseq_coinduction_principle_2 with *)
(*     (X := fun c_k_st => *)
(*             match c_k_st with (c, k, st) => infseq cstep (apply_cont k c, st) end). *)
(*   intros [[c1 k1] st1] ISEQ.  *)
(*   destruct (cinfseq_kinfseq _ _ _ ISEQ) as [c2 [k2 [st2 [KSTEPS ISEQ']]]]. *)
(*   exists (c2, k2, st2); auto. *)
(*   auto. *)
(* Qed. *)
