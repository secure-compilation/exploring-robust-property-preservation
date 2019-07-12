Require Import Bool Arith Omega List Coq.Program.Equality.
Require Import Maps Imp.
Require Import Sequences Semantics.
Require Import List.
Import ListNotations.
Require Import Machine.
Require Import LanguageModel TraceModel ChainModel.
Require Import NonRobustTraceCriterion.

Set Bullet Behavior "Strict Subproofs".

(** * 2. The compilation scheme *)

(** The code for an arithmetic expression [a]
- executes in sequence (no branches)
- deposits the value of [a] at the top of the stack
- preserves the variable state.

This is the familiar translation to "reverse Polish notation".
*)

Fixpoint compile_aexp (a: aexp) : code :=
  match a with
  | ANum n => Iconst n :: nil
  | AId v => Ivar v :: nil
  | APlus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Iadd :: nil
  | AMinus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Isub :: nil
  | AMult a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Imul :: nil
  end.


(** The code [compile_bexp b cond ofs] for a boolean expression [b]
- skips forward the [ofs] following instructions if [b] evaluates to [cond] (a boolean)
- executes in sequence if [b] evaluates to the negation of [cond]
- leaves the stack and the variable state unchanged.

See slides for explanation of the mysterious branch offsets!
*)

Fixpoint compile_bexp (b: bexp) (cond: bool) (ofs: nat) : code :=
  match b with
  | BTrue =>
      if cond then Ibranch_forward ofs :: nil else nil
  | BFalse =>
      if cond then nil else Ibranch_forward ofs :: nil
  | BEq a1 a2 =>
      compile_aexp a1 ++ compile_aexp a2 ++
      (if cond then Ibeq ofs :: nil else Ibne ofs :: nil)
  | BLe a1 a2 =>
      compile_aexp a1 ++ compile_aexp a2 ++
      (if cond then Ible ofs :: nil else Ibgt ofs :: nil)
  | BNot b1 =>
      compile_bexp b1 (negb cond) ofs
  | BAnd b1 b2 =>
      let c2 := compile_bexp b2 cond ofs in
      let c1 := compile_bexp b1 false (if cond then length c2 else ofs + length c2) in
      c1 ++ c2
  end.

(** The code for a command [c]
- updates the variable state as prescribed by [c]
- preserves the stack
- finishes on the next instruction immediately following the generated code.

Again, see slides for explanations of the generated branch offsets.
*)

Fixpoint compile_com (c: com) : code :=
  match c with
  | SKIP =>
      nil
  | (id ::= a) =>
      compile_aexp a ++ Isetvar id :: nil
  | (c1 ;; c2) =>
      compile_com c1 ++ compile_com c2
  | IFB b THEN ifso ELSE ifnot FI =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in
      compile_bexp b false (length code_ifso + 1)
      ++ code_ifso
      ++ Ibranch_forward (length code_ifnot)
      :: code_ifnot
  | WHILE b DO body END =>
      let code_body := compile_com body in
      let code_test := compile_bexp b false (length code_body + 1) in
      code_test
      ++ code_body
      ++ Ibranch_backward (length code_test + length code_body + 1)
      :: nil
  | OUT a =>
    compile_aexp a ++ Iout :: nil
  end.

(** The code for a program [p] (a command) is similar, but terminates
  cleanly on an [Ihalt] instruction. *)

Definition compile_program (p: com) : code :=
  compile_com p ++ Ihalt :: nil.

(** *** Exercise (1 star_tr, recommended) *)
(** The last example shows a slight inefficiency in the code generated for
  [IFB ... THEN ... ELSE SKIP FI].  How would you change [compile_com]
  to generate better code?  Hint: ponder the following function. *)

Definition smart_Ibranch_forward (ofs: nat) : code :=
  if beq_nat ofs 0 then nil else Ibranch_forward(ofs) :: nil.

(** * 3. Semantic preservation *)

(** ** Auxiliary results about code sequences. *)

(** To reason about the execution of compiled code, we need to consider
  code sequences [C2] that are at position [pc] in a bigger code
  sequence [C = C1 ++ C2 ++ C3].  The following predicate
  [codeseq_at C pc C2] does just this. *)

Inductive codeseq_at: code -> nat -> code -> Prop :=
  | codeseq_at_intro: forall C1 C2 C3 pc,
      pc = length C1 ->
      codeseq_at (C1 ++ C2 ++ C3) pc C2.

(** We show a number of no-brainer lemmas about [code_at] and [codeseq_at],
  then populate a "hint database" so that Coq can use them automatically. *)

Lemma code_at_app:
  forall i c2 c1 pc,
  pc = length c1 ->
  code_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; simpl; intros; subst pc; auto.
Qed.

Lemma codeseq_at_head:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  code_at C pc = Some i.
Proof.
  intros. inversion H. simpl. apply code_at_app. auto.
Qed.

Lemma codeseq_at_tail:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  codeseq_at C (pc + 1) C'.
Proof.
  intros. inversion H. 
  change (C1 ++ (i :: C') ++ C3)
    with (C1 ++ (i :: nil) ++ C' ++ C3).
  rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed. 

Lemma codeseq_at_app_left:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C pc C1.
Proof.
  intros. inversion H. rewrite app_ass. constructor. auto.
Qed.

Lemma codeseq_at_app_right:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inversion H. rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed.

Lemma codeseq_at_app_right2:
  forall C pc C1 C2 C3,
  codeseq_at C pc (C1 ++ C2 ++ C3) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inversion H. repeat rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
Qed.

Hint Resolve codeseq_at_head codeseq_at_tail codeseq_at_app_left codeseq_at_app_right codeseq_at_app_right2: codeseq.

Ltac normalize :=
  repeat rewrite app_length in *;
  repeat rewrite plus_assoc in *;
  repeat rewrite plus_0_r in *;
  simpl in *.

(** ** Correctness of generated code for expressions. *)

(** Remember the informal specification we gave for the code generated
  for an arithmetic expression [a].  It should
- execute in sequence (no branches)
- deposit the value of [a] at the top of the stack
- preserve the variable state.

We now prove that the code [compile_aexp a] fulfills this contract.
The proof is a nice induction on the structure of [a]. *)

Lemma compile_aexp_correct:
  forall C st a pc stk,
  codeseq_at C pc (compile_aexp a) ->
  star_tr (transition C)
       (pc, stk, st) nil
       (pc + length (compile_aexp a), aeval st a :: stk, st).
Proof.
  induction a; simpl; intros.

- (* ANum *)
  apply star_tr_one. apply trans_const. eauto with codeseq. 

- (* AId *)
  apply star_tr_one. apply trans_var. eauto with codeseq. 

- (* APlus *)
  replace ([] : list nat) with ([] ++ []: list nat).
  replace (aeval st a1 + aeval st a2 :: stk) with ([aeval st a1 + aeval st a2] ++ stk).
  eapply star_tr_trans.
  apply IHa1. eauto with codeseq. 
  replace ([] : list nat) with ([] ++ [] : list nat).
  eapply star_tr_trans.
  apply IHa2. eauto with codeseq. 
  apply star_tr_one. normalize. apply trans_add. eauto with codeseq.
  reflexivity.
  reflexivity.
  reflexivity.

- (* AMinus *)
  replace ([] : list nat) with ([] ++ []: list nat).
  replace (aeval st a1 + aeval st a2 :: stk) with ([aeval st a1 + aeval st a2] ++ stk).
  eapply star_tr_trans.
  apply IHa1. eauto with codeseq. 
  replace ([] : list nat) with ([] ++ [] : list nat).
  eapply star_tr_trans.
  apply IHa2. eauto with codeseq. 
  apply star_tr_one. normalize. apply trans_sub. eauto with codeseq.
  reflexivity.
  reflexivity.
  reflexivity.

- (* AMult *)
  replace ([] : list nat) with ([] ++ []: list nat).
  replace (aeval st a1 + aeval st a2 :: stk) with ([aeval st a1 + aeval st a2] ++ stk).
  eapply star_tr_trans.
  apply IHa1. eauto with codeseq. 
  replace ([] : list nat) with ([] ++ [] : list nat).
  eapply star_tr_trans.
  apply IHa2. eauto with codeseq. 
  apply star_tr_one. normalize. apply trans_mul. eauto with codeseq.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

(** Here is a similar proof for the compilation of boolean expressions. *)

Lemma compile_bexp_correct:
  forall C st b cond ofs pc stk,
  codeseq_at C pc (compile_bexp b cond ofs) ->
  star_tr (transition C)
       (pc, stk, st) nil
       (pc + length (compile_bexp b cond ofs) + if eqb (beval st b) cond then ofs else 0, stk, st).
Proof.
  induction b; simpl; intros.

- (* BTrue *)
  destruct cond; simpl.
  + (* BTrue, true *)
    apply star_tr_one. apply trans_branch_forward with ofs. eauto with codeseq. auto.
  + (* BTrue, false *)
    repeat rewrite plus_0_r. apply star_tr_refl.
 
- (* BFalse *)
  destruct cond; simpl.
  + (* BFalse, true *)
    repeat rewrite plus_0_r. apply star_tr_refl.
  + (* BFalse, false *)
    apply star_tr_one. apply trans_branch_forward with ofs. eauto with codeseq. auto.

- (* BEq *)
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  eapply star_tr_trans. 
  apply compile_aexp_correct with (a := a). eauto with codeseq. 
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  eapply star_tr_trans.
  apply compile_aexp_correct with (a := a0). eauto with codeseq. 
  apply star_tr_one. normalize.
  destruct cond.
  + (* BEq, true *)
    apply trans_beq with ofs. eauto with codeseq.
    destruct (beq_nat (aeval st a) (aeval st a0)); simpl; omega.
  + (* BEq, false *)
    apply trans_bne with ofs. eauto with codeseq. 
    destruct (beq_nat (aeval st a) (aeval st a0)); simpl; omega.

- (* BLe *)
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  eapply star_tr_trans. 
  apply compile_aexp_correct with (a := a). eauto with codeseq. 
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  eapply star_tr_trans.
  apply compile_aexp_correct with (a := a0). eauto with codeseq. 
  apply star_tr_one. normalize.
  destruct cond.
  + (* BLe, true *)
    apply trans_ble with ofs. eauto with codeseq.
    destruct (leb (aeval st a) (aeval st a0)); simpl; omega.
  + (* BLe, false *)
    apply trans_bgt with ofs. eauto with codeseq. 
    destruct (leb (aeval st a) (aeval st a0)); simpl; omega.

- (* BNot *)
  replace (eqb (negb (beval st b)) cond)
     with (eqb (beval st b) (negb cond)).
  apply IHb; auto. 
  destruct (beval st b); destruct cond; auto.

- (* BAnd *)
  set (code_b2 := compile_bexp b2 cond ofs) in *.
  set (ofs' := if cond then length code_b2 else ofs + length code_b2) in *.
  set (code_b1 := compile_bexp b1 false ofs') in *.
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  apply star_tr_trans with (pc + length code_b1 + (if eqb (beval st b1) false then ofs' else 0), stk, st).
  apply IHb1. eauto with codeseq.
  destruct cond.
  + (* BAnd, true *)
    destruct (beval st b1); simpl.
    * (* b1 evaluates to true *)
      normalize. apply IHb2. eauto with codeseq. 
    * (* b1 evaluates to false *)
      normalize. apply star_tr_refl.
  + (* BAnd, false *)
    destruct (beval st b1); simpl.
    * (* b1 evaluates to true *)
      normalize. apply IHb2. eauto with codeseq. 
    * (* b1 evaluates to false *)
      replace ofs' with (length code_b2 + ofs). normalize. apply star_tr_refl.
      unfold ofs'; omega.
Qed.

(** ** Correctness of generated code for commands: terminating case. *)

Lemma compile_com_correct_terminating:
  forall C st c st' l,
  c / st \\ st' --> l ->
  forall stk pc,
  codeseq_at C pc (compile_com c) ->
  star_tr (transition C)
       (pc, stk, st) l
       (pc + length (compile_com c), stk, st').
Proof.
  induction 1; intros stk pc AT.

- (* SKIP *)
  simpl in *. rewrite plus_0_r. apply star_tr_refl.

- (* := *)
  simpl in *. subst n.
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  eapply star_tr_trans. apply compile_aexp_correct. eauto with codeseq.
  apply star_tr_one. normalize. apply trans_setvar. eauto with codeseq. 

- (* sequence *)
  simpl in *.
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  eapply star_tr_trans. apply IHceval1. eauto with codeseq. 
  normalize. apply IHceval2. eauto with codeseq. 

- (* if true *)
  simpl in *.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  replace l with ([] ++ l); try reflexivity.
  eapply star_tr_trans. 
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq. 
  rewrite H. simpl. rewrite plus_0_r. fold codeb. normalize.
  replace l with (l ++ []).
  eapply star_tr_trans. apply IHceval. eauto with codeseq. 
  apply star_tr_one. eapply trans_branch_forward. eauto with codeseq. omega.
  apply app_nil_r.

- (* if false *)
  simpl in *.
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  replace l with ([] ++ l); try reflexivity.
  eapply star_tr_trans. 
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq. 
  rewrite H. simpl. fold codeb. normalize.
  replace (pc + length codeb + length code1 + S(length code2))
     with (pc + length codeb + length code1 + 1 + length code2).
  apply IHceval. eauto with codeseq. omega. 

- (* while false *)
  simpl in *. 
  replace ([] : list nat) with ([] ++ []: list nat); try reflexivity.
  eapply star_tr_trans.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length (compile_com c) + 1). 
  eauto with codeseq.
  rewrite H. simpl. normalize. apply star_tr_refl.

- (* while true *)
  apply star_tr_trans with (pc, stk, st').
  simpl in *.
  replace l with ([] ++ l); try reflexivity.
  eapply star_tr_trans.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length (compile_com c) + 1). 
  eauto with codeseq. 
  rewrite H; simpl. rewrite plus_0_r.
  replace l with (l ++ []).
  eapply star_tr_trans. apply IHceval1. eauto with codeseq. 
  apply star_tr_one.
  eapply trans_branch_backward. eauto with codeseq. omega.
  apply app_nil_r.
  apply IHceval2. auto.
- (* output *)
  simpl in *. subst n.
  replace [aeval st a] with ([] ++ [aeval st a]).
  eapply star_tr_trans. apply compile_aexp_correct. eauto with codeseq.
  apply star_tr_one. normalize.
  constructor. eauto with codeseq.
  reflexivity.
Qed.

Theorem compile_program_correct_terminating:
  forall c st st' l,
  c / st \\ st' --> l ->
  mach_terminates (compile_program c) st st' l.
Proof.
  intros. unfold compile_program. red.
  exists (length (compile_com c)); split.
  apply code_at_app. auto.
  apply compile_com_correct_terminating with (pc := 0). auto. 
  apply codeseq_at_intro with (C1 := nil). auto.
Qed.


(** ** Correctness of generated code for commands: general case. *)

(** We would like to strengthen the correctness result above so that it
  is not restricted to terminating source programs, but also applies to
  source program that diverge.  To this end, we abandon the big-step
  semantics for commands and switch to the small-step semantics with continuations.
  We then show a simulation theorem, establishing that every transition
  of the small-step semantics in the source program is simulated (in a sense
  to be made precise below) by zero, one or several transitions of the
  machine executing the compiled code for the source program. *)

(** Our first task is to relate configurations [(c, k, st)] of the small-step
  semantics with configurations [(C, pc, stk, st)] of the machine.
  We already know how to relate a command [c] with the machine code,
  using the [codeseq_at] predicate.  What needs to be defined is a relation
  between the continuation [k] and the machine code.

  Intuitively, when the machine finishes executing the generated code for
  command [c], that is, when it reaches the program point
  [pc + length(compile_com c)], the machine should continue by executing
  instructions that perform the pending computations described by
  continuation [k], then reach an [Ihalt] instruction to stop cleanly.

  We formalize this intution by the following inductive predicate
  [compile_cont C k pc], which states that, star_trting at program point [pc],
  there are instructions that perform the computations described in [k]
  and reach an [Ihalt] instruction. *)

Inductive compile_cont (C: code): cont -> nat -> Prop :=
  | ccont_stop: forall pc,
      code_at C pc = Some Ihalt ->
      compile_cont C Kstop pc
  | ccont_seq: forall c k pc pc',
      codeseq_at C pc (compile_com c) ->
      pc' = pc + length (compile_com c) ->
      compile_cont C k pc' ->
      compile_cont C (Kseq c k) pc
  | ccont_while: forall b c k pc ofs pc' pc'',
      code_at C pc = Some(Ibranch_backward ofs) ->
      pc' = pc + 1 - ofs ->
      codeseq_at C pc' (compile_com (WHILE b DO c END)) ->
      pc'' = pc' + length (compile_com (WHILE b DO c END)) ->
      compile_cont C k pc'' ->
      compile_cont C (Kwhile b c k) pc
  | ccont_branch: forall ofs k pc pc',
      code_at C pc = Some(Ibranch_forward ofs) ->
      pc' = pc + 1 + ofs ->
      compile_cont C k pc' ->
      compile_cont C k pc.

(** Then, a configuration [(c,k,st)] of the small-step semantics matches
  a configuration [(C, pc, stk, st')] of the machine if the following conditions hold:
- The memory states are identical: [st' = st].
- The machine stack is empty: [stk = nil].
- The machine code at point [pc] is the compiled code for [c]:
  [codeseq_at C pc (compile_com c)].
- The machine code at point [pc + length (compile_com c)] matches continuation
  [k], in the sense of [compile_cont] above.
*)

Inductive match_config (C: code): com * cont * state -> configuration -> Prop :=
  | match_config_intro: forall c k st pc,
      codeseq_at C pc (compile_com c) ->
      compile_cont C k (pc + length (compile_com c)) ->
      match_config C (c, k, st) (pc, nil, st).



(** Finding an appropriate "anti-stuttering" measure is a bit of a black art.
After trial and error, we find that the following measure works.  It is
the sum of the sizes of the command [c] under focus and all the commands
appearing in the continuation [k]. *)

Fixpoint com_size (c: com) : nat :=
  match c with
  | SKIP => 1
  | x ::= a => 1
  | (c1 ;; c2) => com_size c1 + com_size c2 + 1
  | IFB b THEN ifso ELSE ifnot FI => com_size ifso + com_size ifnot + 1
  | WHILE b DO c1 END => com_size c1 + 1
  | OUT _ => 1
  end.

Remark com_size_nonzero: forall c, com_size c > 0. 
Proof.
  induction c; simpl; omega.
Qed.

Fixpoint cont_size (k: cont) : nat :=
  match k with
  | Kstop => 0
  | Kseq c k' => com_size c + cont_size k'
  | Kwhile b c k' => cont_size k'
  end.

Definition measure (impconf: com * cont * state) : nat :=
  match impconf with (c, k, m) => com_size c + cont_size k end.

(** A few technical lemmas to help with the simulation proof. *)

Lemma compile_cont_Kstop_inv:
  forall C pc m,
  compile_cont C Kstop pc ->
  exists pc',
    star_tr (transition C) (pc, nil, m) [] (pc', nil, m)
  /\ code_at C pc' = Some Ihalt.
Proof.
  intros. dependent induction H. 
- exists pc; split. apply star_tr_refl. auto.
- destruct IHcompile_cont as [pc'' [A B]]; auto.
  exists pc''; split; auto.
  replace (star_tr (transition C) (pc, [], m) [] (pc'', [], m))
          with (star_tr (transition C) (pc, [], m) ([] ++ []) (pc'', [], m)).
  eapply star_tr_step; eauto. eapply trans_branch_forward; eauto.
  reflexivity.
Qed.

Lemma compile_cont_Kseq_inv:
  forall C c k pc m,
  compile_cont C (Kseq c k) pc ->
  exists pc',
    star_tr (transition C) (pc, nil, m) [] (pc', nil, m)
  /\ codeseq_at C pc' (compile_com c)
  /\ compile_cont C k (pc' + length(compile_com c)).
Proof.
  intros. dependent induction H. 
  exists pc; split. apply star_tr_refl. split; congruence. 
  destruct (IHcompile_cont _ _ eq_refl) as [pc'' [A [B D]]].
  exists pc''; split; auto. 
  replace (star_tr (transition C) (pc, [], m) [] (pc'', [], m))
          with (star_tr (transition C) (pc, [], m) ([] ++ []) (pc'', [], m)).
  eapply star_tr_step; eauto. eapply trans_branch_forward; eauto. 
  reflexivity. 
Qed.

Lemma compile_cont_Kwhile_inv:
  forall C b c k pc m,
  compile_cont C (Kwhile b c k) pc ->
  exists pc', 
  plus_tr (transition C) (pc, nil, m) [] (pc', nil, m)
  /\ codeseq_at C pc' (compile_com (WHILE b DO c END))
  /\ compile_cont C k (pc' + length(compile_com (WHILE b DO c END))).
Proof.
  intros. dependent induction H.
- exists (pc + 1 - ofs); split.
  apply plus_tr_one. eapply trans_branch_backward; eauto. 
  split; congruence.
- destruct (IHcompile_cont _ _ _ (refl_equal _)) as [pc'' [A [B D]]].
  exists pc''; split; auto.
  replace (plus_tr (transition C) (pc, [], m) [] (pc'', [], m)) with
      (plus_tr (transition C) (pc, [], m) ([] ++ []) (pc'', [], m)).

  eapply plus_tr_left. eapply trans_branch_forward; eauto.
  apply plus_tr_star_tr; eauto.
  reflexivity.
Qed.

Remark code_at_inv:
  forall C pc i, code_at C pc = Some i -> exists C1, exists C2, C = C1 ++ C2 /\ length C1 = pc.
Proof.
  induction C; simpl; intros.
  inversion H.
  destruct pc. inversion H. exists (@nil instruction); exists (i :: C); auto. 
  destruct (IHC _ _ H) as [C1 [C2 [A B]]].
  exists (a :: C1); exists C2; split. simpl; congruence. simpl; congruence.
Qed.

Remark code_at_codeseq:
  forall C pc i, code_at C pc = Some i -> codeseq_at C pc nil.
Proof.
  intros. destruct (code_at_inv _ _ _ H) as [C1 [C2 [A B]]]. 
  subst. change C2 with (nil ++ C2). constructor. auto.
Qed.

Lemma match_config_skip:
  forall C k m pc,
  compile_cont C k pc ->
  match_config C (SKIP, k, m) (pc, nil, m).
Proof.
  intros C.
  assert (forall k pc, compile_cont C k pc -> codeseq_at C pc nil).
    induction 1.
    eapply code_at_codeseq; eauto.
    change (compile_com c) with (nil ++ compile_com c) in H. eauto with codeseq.
    eapply code_at_codeseq; eauto.
    eapply code_at_codeseq; eauto.
  intros. constructor. simpl. eauto. simpl. rewrite plus_0_r; auto.
Qed.

(** At long last, we can state and prove the right simulation diagram. *)

Lemma simulation_step:
  forall C impstate1 impstate2 machstate1 l,
  kstep impstate1 l impstate2 ->
  match_config C impstate1 machstate1 ->
  exists machstate2,
      (plus_tr (transition C) machstate1 l machstate2
       \/ (star_tr (transition C) machstate1 l machstate2 /\ measure impstate2 < measure impstate1))
   /\ match_config C impstate2 machstate2.
Proof.
  intros until l; intros KSTEP MATCH. 
  inversion KSTEP; clear KSTEP; subst; inversion MATCH; clear MATCH; subst; simpl in *.

- (* assign *)
  econstructor; split.
  left.
  replace ([] : list nat) with ([] ++ [] : list (ev event)).
  eapply plus_tr_right. eapply compile_aexp_correct; eauto with codeseq.
  eapply trans_setvar; eauto with codeseq. 
  reflexivity.
  normalize. apply match_config_skip. auto.

- (* seq *)
  econstructor; split.
  right; split. apply star_tr_refl. omega. 
  normalize. constructor. eauto with codeseq. eapply ccont_seq; eauto with codeseq. 

- (* if true *)
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq.
  omega.
  rewrite H; simpl. fold codeb. normalize. constructor; eauto with codeseq. 
  eapply ccont_branch; eauto with codeseq. 
  change (S (length code2)) with (1 + length code2) in H5. normalize. auto.

- (* if false *)
  set (code1 := compile_com c1) in *.
  set (codeb := compile_bexp b false (length code1 + 1)) in *.
  set (code2 := compile_com c2) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length code1 + 1).
  eauto with codeseq.
  omega.
  rewrite H; simpl. fold codeb. normalize. constructor; eauto with codeseq. 
  change (S (length code2)) with (1 + length code2) in H5. normalize. auto.

- (* while true *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b false (length codec + 1)) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length codec + 1).
  eauto with codeseq.
  omega.
  rewrite H; simpl. fold codeb. normalize. constructor; eauto with codeseq.
  fold codec.
  assert (PC: pc + length codeb + length codec + 1 - (length codeb + length codec + 1) = pc)
      by omega.
  eapply ccont_while; eauto with codeseq. rewrite PC; auto. rewrite PC.
  simpl. normalize. auto.

- (* while false *)
  set (codec := compile_com c) in *.
  set (codeb := compile_bexp b false (length codec + 1)) in *.
  econstructor; split.
  right; split.
  apply compile_bexp_correct with (b := b) (cond := false) (ofs := length codec + 1).
  eauto with codeseq.
  generalize (com_size_nonzero c). omega. 
  rewrite H; simpl. fold codeb. normalize. apply match_config_skip. auto. 

- (* skip seq *)
  normalize.
  destruct (compile_cont_Kseq_inv _ _ _ _ st H4) as [pc' [X [Y Z]]].
  econstructor; split.
  right; split. eexact X. omega.
  constructor; auto. 

- (* skip while *)
  normalize.
  destruct (compile_cont_Kwhile_inv _ _ _ _ _ st H4) as [pc' [X [Y Z]]].
  econstructor; split.
  left. eexact X. 
  constructor; auto.
- (* out *)
  econstructor; split. 
  left.
  replace [aeval st a] with ([] ++ [aeval st a]).
  eapply plus_tr_right.
  eapply compile_aexp_correct; eauto with codeseq.
  constructor; eauto with codeseq.
  reflexivity.
  apply match_config_skip.
  now normalize.
Qed.

(** Simulation diagrams such as [simulation_step] above imply semantic preservation
  for terminating programs and for diverging programs.  We now develop a generic
  proof of this fact that we can reuse later for other program transformations. *)

Section SIMULATION_DIAGRAM.

(** The generic proof is parameterized over the small-step semantics for the
  source and target languages, and over an invariant between their states. *)

  Variable event : Type.

Variable state1: Type.	     (**r the type of configurations for the source language *)
Variable step1: state1 -> list event -> state1 -> Prop.   (**r the small-step semantics for the source language *)

Variable state2: Type.	     (**r the type of configurations for the target language *)
Variable step2: state2 -> list event -> state2 -> Prop.   (**r the small-step semantics for the target language *)

Variable match_states: state1 -> state2 -> Prop.  (**r the invariant *)

Variable measure: state1 -> nat.                  (**r the anti-stuttering measure *)

Hypothesis simulation :
  forall S1 S1' S2 l,
    step1 S1 l S1' -> match_states S1 S2 ->
    exists S2',
      (plus_tr step2 S2 l S2' \/ (star_tr step2 S2 l S2' /\ measure S1' < measure S1))
      /\ match_states S1' S2'.

(** We first extend the simulation to finite sequences of source transitions.
  This will show semantic preservation for terminating programs. *)

Lemma simulation_star_tr:
  forall S1 S1' l,
    star_tr step1 S1 l S1' ->
    forall S2, match_states S1 S2 ->
          exists S2', star_tr step2 S2 l S2' /\ match_states S1' S2'.
Proof.
  induction 1; intros.
- (* zero transition *)
  exists S2; split. apply star_tr_refl. auto.
- (* one or more transitions *)
  destruct (simulation _ _ _ _ H H1) as [S2' [P Q]].
  destruct (IHstar_tr _ Q) as [S2'' [U V]].
  exists S2''; split. 
  (* replace l with ([] ++ l); try reflexivity. *)
  eapply star_tr_trans; eauto. destruct P. apply plus_tr_star_tr; auto. destruct H2; auto.
  auto.
Qed.

(** Turning to infinite sequences, we first show that the target program
  can always make progress, while preserving the [match_states] relation,
  if the source diverges.  The proof is an induction on the maximal number
  [N] of stutterings the target can make before performing at least one transition. *)

(** It follows that the target performs infinitely many transitions if
  star_trted in a configuration that matches a diverging source configuration. *)

Lemma simulation_infseq_tr:
  forall S1 S2 s,
  infseq_tr step1 s S1 ->
  match_states S1 S2 ->
  infseq_tr step2 s S2.
Proof.
  assert (forall S1 S2 s,
             infseq_tr step1 s S1 ->
             match_states S1 S2 ->
             infseq_tr_N step2 s (measure S1) S2).
  {
    clear -simulation.
    cofix Hfix; intros S1 S2 s H H0.
    inversion H; subst; clear H.
    destruct (simulation _ _ _ _ H1 H0) as [S2' [[Hplus | [Hstar Hmeas]] Hmatch]].
    - eapply infseq_tr_N_plus; eauto.
    - eapply infseq_tr_N_star; eauto.
  }
  intros S1 S2 s H0 H1.
  eapply infseq_tr_N_infseq_tr. eauto.
Qed.

Lemma simulation_infseq_silent :
  forall S1 S2,
    infseq_silent step1 S1 ->
    match_states S1 S2 ->
    infseq_silent step2 S2.
Proof.
  assert (forall S1 S2, 
             infseq_silent step1 S1 ->
             match_states S1 S2 ->
             infseq_silent_N step2 (measure S1) S2).
  {
    clear -simulation.
    cofix Hfix; intros S1 S2 H H0.
    inversion H; subst; clear H.
    destruct (simulation _ _ _ _ H1 H0) as [S2' [[Hplus | [Hstar Hmeas]] Hmatch]].
    - eapply infseq_silent_N_plus; eauto.
    - eapply infseq_silent_N_star; eauto.
  }
  intros S1 S2 H0 H1.
  eapply infseq_silent_N_infseq_silent. eauto.
Qed.




End SIMULATION_DIAGRAM.
(** We now apply these results to the Imp compiler.  We first obtain
  an alternate proof of semantic preservation for terminating Imp programs. *)

Lemma match_config_initial:
  forall c st,
  match_config (compile_program c) (c, Kstop, st) (0, nil, st).
Proof.
  intros. constructor.
  change (compile_program c) with (nil ++ compile_com c ++ Ihalt :: nil). constructor. auto.
  simpl. unfold compile_program. constructor. apply code_at_app. auto.
Qed.

Theorem compile_program_correct_terminating_2:
  forall c st st' l,
  kterminates c st st' l ->
  mach_terminates (compile_program c) st st' l.
Proof.
  intros.
  assert (exists machconf2, 
           star_tr (transition (compile_program c)) (0, nil, st) l machconf2
           /\ match_config (compile_program c) (SKIP, Kstop, st') machconf2).
  eapply simulation_star_tr; eauto. eapply simulation_step. apply match_config_initial.
  destruct H0 as [machconf2 [STAR_TR MS]]. 
  inversion MS; subst. simpl in *. normalize. 
  destruct (compile_cont_Kstop_inv _ _ st' H5) as [pc' [A B]].
  red. exists pc'; split. auto.
  replace (l) with (l ++ [] : list (ev event)).
  eapply star_tr_trans; eauto.
  now apply app_nil_r.
Qed.

(** More interestingly, we also prove semantic preservation for diverging
  Imp programs. *)

Theorem compile_program_correct_diverging:
  forall c st s,
  kdiverges c st s ->
  mach_diverges (compile_program c) st s.
Proof.
  intros; red; intros. 
  eapply simulation_infseq_tr with (match_states := match_config (compile_program c)); eauto.
  eapply simulation_step. apply match_config_initial.
Qed.

Theorem compile_program_correct_silent:
  forall c st st' l,
    ksilent c st st' l->
    mach_silent (compile_program c) st st' l.
Proof.
  intros.
  destruct H as [c' [k' [H1 H2]]].
  assert (exists machconf2, star_tr (transition (compile_program c)) (0, nil, st) l machconf2
                       /\ match_config (compile_program c) (c',k', st') machconf2).
  eapply simulation_star_tr; eauto. eapply simulation_step. apply match_config_initial.
  destruct H as [machconf2 [STAR_TR MS]].
  inversion MS; subst. simpl in *.
  normalize.
  red.
  exists pc, nil.
  split.
  eauto.
  eapply simulation_infseq_silent with (match_states := match_config (compile_program c)); eauto.
  eapply simulation_step. 
Qed.



Section Traces.
  Definition event := Imp.event.
  Definition endstate := {| es := unit; an_es := tt |}.
  Definition trace := @TraceModel.trace event endstate.
End Traces.

Section Source.

  Definition sprg := com.
  Definition spar := sprg.
  Definition sctx := unit.
  Definition splug (p : spar) (c : sctx) := p.

  Definition source := {| prg := sprg; par := spar; ctx := sctx; plug := splug |}.

  Definition semS (p : sprg) (t : trace) : Prop :=
    match t with
    | tstop l e => exists st', kterminates p empty_state st' l
    | tsilent l => exists st', ksilent p empty_state st' l
    | tstream s => kdiverges p empty_state s
    end.

  Lemma non_empty_semS : forall W, exists t, semS W t.
  Proof.
  Admitted.

  Definition semanticsS : Semantics source trace :=
    {| sem := semS : prg source -> trace -> Prop;
       non_empty_sem := non_empty_semS |}.

End Source.

Section Target.

  Definition tprg := code.
  Definition tpar := tprg.
  Definition tctx := unit.
  Definition tplug (p : tpar) (c : tctx) := p.

  Definition target := {| prg := tprg; par := tpar; ctx := tctx; plug := tplug |}.

  Definition semT (p : tprg) (t : trace) : Prop :=
    match t with
    | tstop l e => exists st', mach_terminates p (empty_state) st' l
    | tsilent l => exists st', mach_silent p empty_state st' l
    | tstream s => mach_diverges p empty_state s
    end.

  Lemma non_empty_semT : forall W, exists t, semT W t.
  Proof.
  Admitted.

  Definition semanticsT : Semantics target trace :=
    {| sem := semT : prg target -> trace -> Prop;
       non_empty_sem := non_empty_semT |}.

End Target.


Section CompilationChain.

  Definition compile : prg source -> prg target := compile_program.
  Hint Unfold compile.

  Definition compiler : CompilationChain source target :=
    {| compile_whole := compile;
       compile_par := compile;
       compile_ctx := fun x => x |}.

End CompilationChain.

Definition rel := eq : trace -> trace -> Prop.
Hint Unfold rel.

Definition rel_TC := rel_TC compiler semanticsS semanticsT rel.

Definition rel_TC_fwd := forall W t, semS W t -> exists s, rel s t /\ semT (compile W) s.

Lemma target_determinism : forall W s1 s2,
    semT W s1 ->
    semT W s2 ->
    s1 = s2.
Proof.
Admitted.

Lemma rel_TC_fwd_rel_TC : rel_TC_fwd -> rel_TC.
Proof.
  unfold rel_TC_fwd, rel_TC, NonRobustTraceCriterion.rel_TC.
  intros H W t H0.
  exists t; split; eauto.
  destruct (non_empty_semS W) as [s Hs].
  assert (Hs' := Hs).
  apply H in Hs'.
  destruct Hs' as [t0 [Heq Ht0]].
  unfold rel in Heq; subst t0.
  assert (s = t) by now apply target_determinism with (W := compile W).
  now subst.
Qed.

Theorem correctness : rel_TC.
Proof.
  apply rel_TC_fwd_rel_TC.
  unfold rel_TC_fwd.
  intros W t H; simpl in H.
  exists t; split; eauto.
  destruct t as [l e | l | s].
  - simpl in *.
    destruct H as [st' Hterm].
    apply compile_program_correct_terminating_2 in Hterm.
    now (exists st').
  - simpl in *.
    destruct H as [st' Hsil].
    apply compile_program_correct_silent in Hsil.
    now (exists st').
  - simpl in *.
    apply compile_program_correct_diverging in H.
    assumption.
Qed.

