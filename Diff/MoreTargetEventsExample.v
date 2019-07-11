Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FSetWeakList.
Require Import TraceModel.
Require Import LanguageModel.
Require Import ChainModel.
Require Import RobustTraceCriterion.

Set Bullet Behavior "Strict Subproofs".

(* Simple binary location: program or context. *)
Inductive turn : Set :=
| ProgramTurn
| ContextTurn.

(* Name-function maps, with some parts stubbed. *)
Module DecidableString : DecidableType.
  Definition t := string.
  Axiom eq : string -> string -> Prop.
  Axiom eq_refl : forall x, eq x x.
  Axiom eq_sym : forall x y, eq x y -> eq y x.
  Axiom eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Axiom eq_dec : forall x y, {eq x y} + {~ eq x y}.
End DecidableString.

Module StringMap : WS with Module E := DecidableString :=
  FMapWeakList.Make DecidableString.

Module StringMapFacts := WFacts_fun DecidableString StringMap.

(* And function name sets, for interfacing purposes. *)
Module StringSet := FSetWeakList.Make DecidableString.
Notation "∅" := StringSet.empty (at level 70, no associativity).
Notation "s1 ∪ s2" := (StringSet.union s1 s2) (at level 70, right associativity).

Definition elements_set (A : Type) (m : StringMap.t A) : StringSet.t :=
  let keys := map fst (StringMap.elements m) in
  fold_left (fun acc key => StringSet.add key acc) keys StringSet.empty.

(* A helper. *)
Remark forall_app : forall A f (l1 l2 : list A),
  Forall f l1 -> Forall f l2 -> Forall f (l1 ++ l2).
Proof.
  induction l1; intros l2 H1 H2.
  - now eauto.
  - simpl. inversion H1. now eauto.
Qed.

(* Source language. *)
Module Source.
  (* Base expressions. *)
  Inductive expr : Type :=
  | Const : nat -> expr
  | Plus  : expr -> expr -> expr
  | IfLe  : expr -> expr -> expr -> expr -> expr
  | Seq   : expr -> expr -> expr
  | Out   : expr -> expr
  | Fun   : StringMap.key -> expr -> expr.

  (* Function expressions. *)
  Inductive fexpr : Type :=
  | FConst : nat -> fexpr
  | FPlus  : fexpr -> fexpr -> fexpr
  | FIfLe  : fexpr -> fexpr -> fexpr -> fexpr -> fexpr
  | FSeq   : fexpr -> fexpr -> fexpr
  | FOut   : fexpr -> fexpr
  | FArg   : fexpr.

  (* Function types. *)
  Definition funmap := StringMap.t fexpr.
  Definition funmap_turn := StringMap.t (turn * fexpr).
  Definition funset := StringSet.t.

  (* Some additional helpers to write properties. *)
  Definition funmap_bodies (fs : funmap) : list fexpr :=
    List.map snd (StringMap.elements fs).

  Definition funmap_turn_bodies (fs : funmap_turn) : funmap :=
    StringMap.map snd fs.

  (* Well-formed calls. *)
  Inductive well_formed_calls (fs : funmap_turn) : expr -> Prop :=
  | CallsConst : forall n,
      well_formed_calls fs (Const n)
  | CallsPlus : forall e1 e2,
      well_formed_calls fs e1 -> well_formed_calls fs e2 ->
      well_formed_calls fs (Plus e1 e2)
  | CallsIfLe : forall econd1 econd2 ethen eelse,
      well_formed_calls fs econd1 -> well_formed_calls fs econd2 ->
      well_formed_calls fs ethen -> well_formed_calls fs eelse ->
      well_formed_calls fs (IfLe econd1 econd2 ethen eelse)
  | CallsSeq : forall e1 e2,
      well_formed_calls fs e1 -> well_formed_calls fs e2 ->
      well_formed_calls fs (Seq e1 e2)
  | CallsOut : forall e,
      well_formed_calls fs e ->
      well_formed_calls fs (Out e)
  | CallsFun id earg :
      StringMap.mem id fs = true ->
      well_formed_calls fs earg -> well_formed_calls fs (Fun id earg).

  (* A simple notion of closed program with implicit, exact interfaces. *)
  Fixpoint funs (e : expr) : funset :=
    match e with
    | Const _ => ∅
    | Out e => funs e
    | Plus e1 e2 | Seq e1 e2 => funs e1 ∪ funs e2
    | IfLe e1 e2 e3 e4 => funs e1 ∪ funs e2 ∪ funs e3 ∪ funs e3
    | Fun f e => StringSet.add f (funs e)
    end.

  Definition closed (fs : funmap_turn) (e : expr) : bool :=
    StringSet.equal (elements_set _ fs) (funs e).

  (* Programs and contexts. *)
  Record par :=
    {
      par_funs : funmap;
      par_main : expr;
    }.

  Record ctx :=
    {
      ctx_funs : funmap;
    }.

  (* Record prg_wf (funs : funmap_turn) (main : expr) := *)
  (*   { *)
  (*     prg_wf_calls : well_formed_calls funs main *)
  (*   }. *)

  Record prg :=
    {
      prg_funs : funmap_turn;
      prg_main : expr;
    }.

  Definition prg_wf (p : prg) : Prop :=
    well_formed_calls (prg_funs p) (prg_main p).

  (* Linking. Assume main in the program and combine functions from program and
     context with tags to remember provenance. *)
  Definition link_fun (par_fun ctx_fun : option fexpr) :=
    match par_fun, ctx_fun with
    | Some f, _ => Some (ProgramTurn, f)
    | _, Some f => Some (ContextTurn, f)
    | _, _ => None
    end.

  Definition link_funmaps (funs_p funs_c : funmap) : funmap_turn :=
    StringMap.map2 link_fun funs_p funs_c.

  Definition link_funs (p : par) (c : ctx) : funmap_turn :=
    link_funmaps (par_funs p) (ctx_funs c).

  (* Lemma link_wf  (p : par) (c : ctx) : *)
  (*   closed (link_funs p c) (par_main p) = true -> *)
  (*   par_wf (par_funs p) (par_main p) -> *)
  (*   ctx_wf (ctx_funs c) -> *)
  (*   prg_wf (link_funs p c) (par_main p). *)
  (* Admitted. *)

  Definition link (p : par) (c : ctx) : prg :=
    Build_prg (link_funs p c) (par_main p).

  (* Traces as lists of events. *)
  Inductive event :=
  | Result : nat -> event
  | Output : nat -> event.

  Inductive reg_event : event -> Prop :=
  | RE_Output : forall n, reg_event (Output n).

  Definition trace := list event.

  (* Evaluation-based semantics, returns trace. *)
  Inductive eval_fun (arg : nat) : fexpr -> (nat * trace) -> Prop :=
  | FEval_Const : forall n,
      eval_fun arg (FConst n) (n, [])
  | FEval_Plus : forall e1 e2 n1 n2 t1 t2,
      eval_fun arg e1 (n1, t1) -> eval_fun arg e2 (n2, t2) ->
      eval_fun arg (FPlus e1 e2) (n1 + n2, t1 ++ t2)
  | FEval_IfThen : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_fun arg ecomp1 (n1, t1) -> eval_fun arg ecomp2 (n2, t2) ->
      n1 <= n2 -> eval_fun arg ethen (n, t) ->
      eval_fun arg (FIfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | FEval_IfElse : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_fun arg ecomp1 (n1, t1) -> eval_fun arg ecomp2 (n2, t2) ->
      n1 > n2 -> eval_fun arg eelse (n, t) ->
      eval_fun arg (FIfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | FEval_Seq : forall e1 e2 n1 n2 t1 t2,
      eval_fun arg e1 (n1, t1) -> eval_fun arg e2 (n2, t2) ->
      eval_fun arg (FSeq e1 e2) (n2, t1 ++ t2)
  | FEval_Out : forall e n t,
      eval_fun arg e (n, t) ->
      eval_fun arg (FOut e) (n, t ++ [Output n])
  | FEval_Arg :
      eval_fun arg FArg (arg, []).

  Inductive eval_main (fs : funmap_turn) : expr -> (nat * trace) -> Prop :=
  | Eval_Const : forall n,
      eval_main fs (Const n) (n, [])
  | Eval_Plus : forall e1 e2 n1 n2 t1 t2,
      eval_main fs e1 (n1, t1) -> eval_main fs e2 (n2, t2) ->
      eval_main fs (Plus e1 e2) (n1 + n2, t1 ++ t2)
  | Eval_IfThen : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_main fs ecomp1 (n1, t1) -> eval_main fs ecomp2 (n2, t2) ->
      n1 <= n2 -> eval_main fs ethen (n, t) ->
      eval_main fs (IfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | Eval_IfElse : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_main fs ecomp1 (n1, t1) -> eval_main fs ecomp2 (n2, t2) ->
      n1 > n2 -> eval_main fs eelse (n, t) ->
      eval_main fs (IfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | Eval_Seq : forall e1 e2 n1 n2 t1 t2,
      eval_main fs e1 (n1, t1) -> eval_main fs e2 (n2, t2) ->
      eval_main fs (Seq e1 e2) (n2, t1 ++ t2)
  | Eval_Out : forall e n t,
      eval_main fs e (n, t) ->
      eval_main fs (Out e) (n, t ++ [Output n])
  | Eval_Fun : forall id turn earg e arg n targ t,
      StringMap.find id fs = Some (turn, e) ->
      eval_main fs earg (arg, targ) -> eval_fun arg e (n, t) ->
      eval_main fs (Fun id earg) (n, targ ++ t)
  (* Temporary hack covering the bad case. *)
  | Eval_BadFun : forall id earg,
      StringMap.find id fs = None ->
      eval_main fs (Fun id earg) (0, []).
  
  Inductive eval_prg (p : prg) : trace -> Prop :=
  | Eval_Prg : forall n t,
      eval_main (prg_funs p) (prg_main p) (n, t) ->
      eval_prg p (t ++ [Result n]).

  Inductive sem_prg : prg -> trace -> Prop :=
  | SemEval : forall p t, eval_prg p t -> sem_prg p t.

  Remark trace_exists_fun : forall arg e, exists res t, eval_fun arg e (res, t).
  Proof.
    intros arg e. induction e.
    - do 2 eexists. now econstructor.
    - destruct IHe1 as [? [? Hfun1]].
      destruct IHe2 as [? [? Hfun2]].
      do 2 eexists. econstructor; eassumption.
    - destruct IHe1 as [n1 [? Hfun1]].
      destruct IHe2 as [n2 [? Hfun2]].
      destruct IHe3 as [n3 [? Hfun3]].
      destruct IHe4 as [n4 [? Hfun4]].
      destruct (Compare_dec.le_gt_dec n1 n2) as [Hle | Hgt].
      + do 2 eexists. econstructor; eassumption.
      + do 2 eexists. eapply FEval_IfElse; eassumption.
    - destruct IHe1 as [? [? Hfun1]].
      destruct IHe2 as [? [? Hfun2]].
      do 2 eexists. econstructor; eassumption.
    - destruct IHe as [? [? Hfun1]].
      do 2 eexists. econstructor; eassumption.
    - do 2 eexists. econstructor; eassumption.
  Qed.

  Remark trace_exists : forall W : prg, exists t : trace, sem_prg W t.
  Proof.
    intros [funs main].
    induction main.
    - eexists. now do 3 constructor.
    - destruct IHmain1 as [t1 Hsem1];
        inversion Hsem1 as [? ? Hprg1];
        inversion Hprg1 as [? ? Hmain1]; subst.
      destruct IHmain2 as [t2 Hsem2];
        inversion Hsem2 as [? ? Hprg2];
        inversion Hprg2 as [? ? Hmain2]; subst.
      eexists. do 3 constructor; eassumption.
    - destruct IHmain1 as [? Hsem1];
        inversion Hsem1 as [? ? Hprg1];
        inversion Hprg1 as [n1 t1 Hmain1]; subst.
      destruct IHmain2 as [? Hsem2];
        inversion Hsem2 as [? ? Hprg2];
        inversion Hprg2 as [n2 t2 Hmain2]; subst.
      destruct IHmain3 as [? Hsem3];
        inversion Hsem3 as [? ? Hprg3];
        inversion Hprg3 as [n3 t3 Hmain3]; subst.
      destruct IHmain4 as [? Hsem4];
        inversion Hsem4 as [? ? Hprg4];
        inversion Hprg4 as [n4 t4 Hmain4]; subst.
      destruct (Compare_dec.le_gt_dec n1 n2) as [Hle | Hgt].
      + eexists. do 3 econstructor; eassumption.
      + eexists. do 2 constructor. eapply Eval_IfElse; eassumption.
    - destruct IHmain1 as [t1 Hsem1];
        inversion Hsem1 as [? ? Hprg1];
        inversion Hprg1 as [? ? Hmain1]; subst.
      destruct IHmain2 as [t2 Hsem2];
        inversion Hsem2 as [? ? Hprg2];
        inversion Hprg2 as [? ? Hmain2]; subst.
      eexists. do 2 constructor. eapply Eval_Seq; eassumption.
    - destruct IHmain as [t1 Hsem];
        inversion Hsem as [? ? Hprg];
        inversion Hprg as [? ? Hmain]; subst.
      eexists. do 3 constructor; eassumption.
    - destruct IHmain as [? Hsem];
        inversion Hsem as [? ? Hprg];
        inversion Hprg as [n t' Hmain]; subst.
      destruct (StringMap.find k funs) as [[turn e] |] eqn:Hcase.
      + destruct (trace_exists_fun n e) as [? [? Hfun]].
        eexists. do 2 constructor. eapply Eval_Fun; try eassumption.
      + eexists. do 3 constructor; eassumption.
  Qed.

  Inductive wf_trace : trace -> Prop :=
  | WFTrace : forall t t' res,
      t = t' ++ [Result res] -> Forall reg_event t' -> wf_trace t.

  Lemma eval_fun_trace : forall arg e n t,
    eval_fun arg e (n, t) ->
    Forall reg_event t.
  Proof.
    induction e;
      intros res t Heval;
      inversion Heval; subst.
    - now eauto.
    - apply forall_app; now eauto.
    - apply forall_app; [| apply forall_app]; now eauto.
    - apply forall_app; [| apply forall_app]; now eauto.
    - apply forall_app; now eauto.
    - apply forall_app; first now eauto.
      now constructor.
    - now eauto.
  Qed.

  Lemma eval_main_trace : forall funs main n t,
    eval_main funs main (n, t) ->
    Forall reg_event t.
  Proof.
    induction main;
      intros res t Heval;
      inversion Heval; subst.
    - now eauto.
    - apply forall_app; now eauto.
    - apply forall_app; [| apply forall_app]; now eauto.
    - apply forall_app; [| apply forall_app]; now eauto.
    - apply forall_app; now eauto.
    - apply forall_app; first now eauto.
      now constructor.
    - apply forall_app; first now eauto.
      eapply eval_fun_trace; eassumption.
    - now eauto.
  Qed.

  Theorem sem_trace : forall p t, sem_prg p t -> wf_trace t.
  Proof.
    intros p t Hsem.
    inversion Hsem as [? ? Hprg]; subst.
    inversion Hprg as [? ? Hmain]; subst.
    apply eval_main_trace in Hmain.
    now econstructor.
  Qed.

  Definition lang := Build_Language link.
  Definition sem := Build_Semantics lang sem_prg trace_exists.
End Source.

(* Target language. *)
Module Target.
  (* Base expressions. *)
  Inductive expr : Type :=
  | Const : nat -> expr
  | Plus  : expr -> expr -> expr
  | IfLe  : expr -> expr -> expr -> expr -> expr
  | Seq   : expr -> expr -> expr
  | Out   : expr -> expr
  | OutH  : expr -> expr
  | Fun   : StringMap.key -> expr -> expr.

  (* Function expressions. *)
  Inductive fexpr : Type :=
  | FConst : nat -> fexpr
  | FPlus  : fexpr -> fexpr -> fexpr
  | FIfLe  : fexpr -> fexpr -> fexpr -> fexpr -> fexpr
  | FSeq   : fexpr -> fexpr -> fexpr
  | FOut   : fexpr -> fexpr
  | FOutH  : fexpr -> fexpr
  | FArg   : fexpr.

  (* Function types. *)
  Definition funmap := StringMap.t fexpr.
  Definition funmap_turn := StringMap.t (turn * fexpr).
  Definition funset := StringSet.t.

  (* Some additional helpers to write properties. *)
  Definition funmap_bodies (fs : funmap) : list fexpr :=
    List.map snd (StringMap.elements fs).

  Definition funmap_turn_bodies (fs : funmap_turn) : funmap :=
    StringMap.map snd fs.

  (* Well-formed calls. *)
  Inductive well_formed_calls (fs : funmap_turn) : expr -> Prop :=
  | CallsConst : forall n,
      well_formed_calls fs (Const n)
  | CallsPlus : forall e1 e2,
      well_formed_calls fs e1 -> well_formed_calls fs e2 ->
      well_formed_calls fs (Plus e1 e2)
  | CallsIfLe : forall econd1 econd2 ethen eelse,
      well_formed_calls fs econd1 -> well_formed_calls fs econd2 ->
      well_formed_calls fs ethen -> well_formed_calls fs eelse ->
      well_formed_calls fs (IfLe econd1 econd2 ethen eelse)
  | CallsSeq : forall e1 e2,
      well_formed_calls fs e1 -> well_formed_calls fs e2 ->
      well_formed_calls fs (Seq e1 e2)
  | CallsOut : forall e,
      well_formed_calls fs e ->
      well_formed_calls fs (Out e)
  | CallsOutH : forall e,
      well_formed_calls fs e ->
      well_formed_calls fs (OutH e)
  | CallsFun id earg :
      StringMap.mem id fs = true ->
      well_formed_calls fs earg -> well_formed_calls fs (Fun id earg).

  (* A simple notion of closed program with implicit, exact interfaces. *)
  Fixpoint funs (e : expr) : funset :=
    match e with
    | Const _ => ∅
    | Out e | OutH e => funs e
    | Plus e1 e2 | Seq e1 e2 => funs e1 ∪ funs e2
    | IfLe e1 e2 e3 e4 => funs e1 ∪ funs e2 ∪ funs e3 ∪ funs e3
    | Fun f e => StringSet.add f (funs e)
    end.

  Definition closed (fs : funmap_turn) (e : expr) : bool :=
    StringSet.equal (elements_set _ fs) (funs e).

  (* Programs and contexts. *)
  Record par :=
    {
      par_funs : funmap;
      par_main : expr;
    }.

  Record ctx :=
    {
      ctx_funs : funmap;
    }.

  (* Record prg_wf (funs : funmap_turn) (main : expr) := *)
  (*   { *)
  (*     prg_wf_calls : well_formed_calls funs main *)
  (*   }. *)

  Record prg :=
    {
      prg_funs : funmap_turn;
      prg_main : expr;
    }.

  Definition prg_wf (p : prg) : Prop :=
    well_formed_calls (prg_funs p) (prg_main p).

  (* Linking. Assume main in the program and combine functions from program and
     context with tags to remember provenance. *)
  Definition link_fun (par_fun ctx_fun : option fexpr) :=
    match par_fun, ctx_fun with
    | Some f, _ => Some (ProgramTurn, f)
    | _, Some f => Some (ContextTurn, f)
    | _, _ => None
    end.

  Definition link_funmaps (funs_p funs_c : funmap) : funmap_turn :=
    StringMap.map2 link_fun funs_p funs_c.

  Definition link_funs (p : par) (c : ctx) : funmap_turn :=
    link_funmaps (par_funs p) (ctx_funs c).

  (* Lemma link_wf  (p : par) (c : ctx) : *)
  (*   closed (link_funs p c) (par_main p) = true -> *)
  (*   par_wf (par_funs p) (par_main p) -> *)
  (*   ctx_wf (ctx_funs c) -> *)
  (*   prg_wf (link_funs p c) (par_main p). *)
  (* Admitted. *)

  Definition link (p : par) (c : ctx) : prg :=
    Build_prg (link_funs p c) (par_main p).

  (* Traces as lists of events. *)
  Inductive event :=
  | Result : nat -> event
  | Output : nat -> event
  | OutputH : nat -> event.

  Inductive reg_event : event -> Prop :=
  | RE_Output : forall n, reg_event (Output n)
  | RE_OutputH : forall n, reg_event (OutputH n).

  Definition trace := list event.

  (* Evaluation-based semantics, returns trace. *)
  Inductive eval_fun (arg : nat) : fexpr -> (nat * trace) -> Prop :=
  | FEval_Const : forall n,
      eval_fun arg (FConst n) (n, [])
  | FEval_Plus : forall e1 e2 n1 n2 t1 t2,
      eval_fun arg e1 (n1, t1) -> eval_fun arg e2 (n2, t2) ->
      eval_fun arg (FPlus e1 e2) (n1 + n2, t1 ++ t2)
  | FEval_IfThen : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_fun arg ecomp1 (n1, t1) -> eval_fun arg ecomp2 (n2, t2) ->
      n1 <= n2 -> eval_fun arg ethen (n, t) ->
      eval_fun arg (FIfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | FEval_IfElse : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_fun arg ecomp1 (n1, t1) -> eval_fun arg ecomp2 (n2, t2) ->
      n1 > n2 -> eval_fun arg eelse (n, t) ->
      eval_fun arg (FIfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | FEval_Seq : forall e1 e2 n1 n2 t1 t2,
      eval_fun arg e1 (n1, t1) -> eval_fun arg e2 (n2, t2) ->
      eval_fun arg (FSeq e1 e2) (n2, t1 ++ t2)
  | FEval_Out : forall e n t,
      eval_fun arg e (n, t) ->
      eval_fun arg (FOut e) (n, t ++ [Output n])
  | FEval_OutH : forall e n t,
      eval_fun arg e (n, t) ->
      eval_fun arg (FOutH e) (n, t ++ [OutputH n])
  | FEval_Arg :
      eval_fun arg FArg (arg, []).

  Inductive eval_main (fs : funmap_turn) : expr -> (nat * trace) -> Prop :=
  | Eval_Const : forall n,
      eval_main fs (Const n) (n, [])
  | Eval_Plus : forall e1 e2 n1 n2 t1 t2,
      eval_main fs e1 (n1, t1) -> eval_main fs e2 (n2, t2) ->
      eval_main fs (Plus e1 e2) (n1 + n2, t1 ++ t2)
  | Eval_IfThen : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_main fs ecomp1 (n1, t1) -> eval_main fs ecomp2 (n2, t2) ->
      n1 <= n2 -> eval_main fs ethen (n, t) ->
      eval_main fs (IfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | Eval_IfElse : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_main fs ecomp1 (n1, t1) -> eval_main fs ecomp2 (n2, t2) ->
      n1 > n2 -> eval_main fs eelse (n, t) ->
      eval_main fs (IfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | Eval_Seq : forall e1 e2 n1 n2 t1 t2,
      eval_main fs e1 (n1, t1) -> eval_main fs e2 (n2, t2) ->
      eval_main fs (Seq e1 e2) (n2, t1 ++ t2)
  | Eval_Out : forall e n t,
      eval_main fs e (n, t) ->
      eval_main fs (Out e) (n, t ++ [Output n])
  | Eval_OutH : forall e n t,
      eval_main fs e (n, t) ->
      eval_main fs (OutH e) (n, t ++ [OutputH n])
  | Eval_Fun : forall id turn earg e arg n targ t,
      StringMap.find id fs = Some (turn, e) ->
      eval_main fs earg (arg, targ) -> eval_fun arg e (n, t) ->
      eval_main fs (Fun id earg) (n, targ ++ t)
  (* Temporary hack covering the bad case. *)
  | Eval_BadFun : forall id earg,
      StringMap.find id fs = None ->
      eval_main fs (Fun id earg) (0, []).
  
  Inductive eval_prg (p : prg) : trace -> Prop :=
  | Eval_Prg : forall n t,
      eval_main (prg_funs p) (prg_main p) (n, t) ->
      eval_prg p (t ++ [Result n]).

  Inductive sem_prg : prg -> trace -> Prop :=
  | SemEval : forall p t, eval_prg p t -> sem_prg p t.

  Remark trace_exists_fun : forall arg e, exists res t, eval_fun arg e (res, t).
  Proof.
    intros arg e. induction e.
    - do 2 eexists. now econstructor.
    - destruct IHe1 as [? [? Hfun1]].
      destruct IHe2 as [? [? Hfun2]].
      do 2 eexists. econstructor; eassumption.
    - destruct IHe1 as [n1 [? Hfun1]].
      destruct IHe2 as [n2 [? Hfun2]].
      destruct IHe3 as [n3 [? Hfun3]].
      destruct IHe4 as [n4 [? Hfun4]].
      destruct (Compare_dec.le_gt_dec n1 n2) as [Hle | Hgt].
      + do 2 eexists. econstructor; eassumption.
      + do 2 eexists. eapply FEval_IfElse; eassumption.
    - destruct IHe1 as [? [? Hfun1]].
      destruct IHe2 as [? [? Hfun2]].
      do 2 eexists. econstructor; eassumption.
    - destruct IHe as [? [? Hfun1]].
      do 2 eexists. econstructor; eassumption.
    - destruct IHe as [? [? Hfun1]].
      do 2 eexists. econstructor; eassumption.
    - do 2 eexists. econstructor; eassumption.
  Qed.

  Remark trace_exists : forall W : prg, exists t : trace, sem_prg W t.
  Proof.
    intros [funs main].
    induction main.
    - eexists. now do 3 constructor.
    - destruct IHmain1 as [t1 Hsem1];
        inversion Hsem1 as [? ? Hprg1];
        inversion Hprg1 as [? ? Hmain1]; subst.
      destruct IHmain2 as [t2 Hsem2];
        inversion Hsem2 as [? ? Hprg2];
        inversion Hprg2 as [? ? Hmain2]; subst.
      eexists. do 3 constructor; eassumption.
    - destruct IHmain1 as [? Hsem1];
        inversion Hsem1 as [? ? Hprg1];
        inversion Hprg1 as [n1 t1 Hmain1]; subst.
      destruct IHmain2 as [? Hsem2];
        inversion Hsem2 as [? ? Hprg2];
        inversion Hprg2 as [n2 t2 Hmain2]; subst.
      destruct IHmain3 as [? Hsem3];
        inversion Hsem3 as [? ? Hprg3];
        inversion Hprg3 as [n3 t3 Hmain3]; subst.
      destruct IHmain4 as [? Hsem4];
        inversion Hsem4 as [? ? Hprg4];
        inversion Hprg4 as [n4 t4 Hmain4]; subst.
      destruct (Compare_dec.le_gt_dec n1 n2) as [Hle | Hgt].
      + eexists. do 3 econstructor; eassumption.
      + eexists. do 2 constructor. eapply Eval_IfElse; eassumption.
    - destruct IHmain1 as [t1 Hsem1];
        inversion Hsem1 as [? ? Hprg1];
        inversion Hprg1 as [? ? Hmain1]; subst.
      destruct IHmain2 as [t2 Hsem2];
        inversion Hsem2 as [? ? Hprg2];
        inversion Hprg2 as [? ? Hmain2]; subst.
      eexists. do 2 constructor. eapply Eval_Seq; eassumption.
    - destruct IHmain as [t1 Hsem];
        inversion Hsem as [? ? Hprg];
        inversion Hprg as [? ? Hmain]; subst.
      eexists. do 3 constructor; eassumption.
    - destruct IHmain as [? Hsem];
        inversion Hsem as [? ? Hprg];
        inversion Hprg as [n t' Hmain]; subst.
      eexists. do 3 constructor; eassumption.
    - destruct IHmain as [? Hsem];
        inversion Hsem as [? ? Hprg];
        inversion Hprg as [n t' Hmain]; subst.
      destruct (StringMap.find k funs) as [[turn e] |] eqn:Hcase.
      + destruct (trace_exists_fun n e) as [? [? Hfun]].
        eexists. do 2 constructor. eapply Eval_Fun; try eassumption.
      + eexists. do 3 constructor; eassumption.
  Qed.

  Inductive wf_trace : trace -> Prop :=
  | WFTrace : forall t t' res,
      t = t' ++ [Result res] -> Forall reg_event t' -> wf_trace t.

  Lemma eval_fun_trace : forall arg e n t,
    eval_fun arg e (n, t) ->
    Forall reg_event t.
  Proof.
    induction e;
      intros res t Heval;
      inversion Heval; subst.
    - now eauto.
    - apply forall_app; now eauto.
    - apply forall_app; [| apply forall_app]; now eauto.
    - apply forall_app; [| apply forall_app]; now eauto.
    - apply forall_app; now eauto.
    - apply forall_app; first now eauto.
      now repeat constructor.
    - apply forall_app; first now eauto.
      now repeat constructor.
    - now eauto.
  Qed.

  Lemma eval_main_trace : forall funs main n t,
    eval_main funs main (n, t) ->
    Forall reg_event t.
  Proof.
    induction main;
      intros res t Heval;
      inversion Heval; subst.
    - now eauto.
    - apply forall_app; now eauto.
    - apply forall_app; [| apply forall_app]; now eauto.
    - apply forall_app; [| apply forall_app]; now eauto.
    - apply forall_app; now eauto.
    - apply forall_app; first now eauto.
      now repeat constructor.
    - apply forall_app; first now eauto.
      now repeat constructor.
    - apply forall_app; first now eauto.
      eapply eval_fun_trace; eassumption.
    - now eauto.
  Qed.

  Theorem sem_trace : forall p t, sem_prg p t -> wf_trace t.
  Proof.
    intros p t Hsem.
    inversion Hsem as [? ? Hprg]; subst.
    inversion Hprg as [? ? Hmain]; subst.
    apply eval_main_trace in Hmain.
    now econstructor.
  Qed.

  Definition lang := Build_Language link.
  Definition sem := Build_Semantics lang sem_prg trace_exists.
End Target.

(* Compiler. *)
Module Compiler.
  Module S := Source.
  Module T := Target.

  (* Build the identity compiler and define the chain. *)
  Fixpoint comp_expr (e : S.expr) : T.expr :=
    match e with
    | S.Const n => T.Const n
    | S.Plus e1 e2 => T.Plus (comp_expr e1) (comp_expr e2)
    | S.IfLe e1 e2 e3 e4 =>
      T.IfLe (comp_expr e1) (comp_expr e2) (comp_expr e3) (comp_expr e4)
    | S.Seq e1 e2 => T.Seq (comp_expr e1) (comp_expr e2)
    | S.Out e => T.Out (comp_expr e)
    | S.Fun f e => T.Fun f (comp_expr e)
    end.

  Fixpoint comp_fexpr (e : S.fexpr) : T.fexpr :=
    match e with
    | S.FConst n => T.FConst n
    | S.FPlus e1 e2 => T.FPlus (comp_fexpr e1) (comp_fexpr e2)
    | S.FIfLe e1 e2 e3 e4 =>
      T.FIfLe (comp_fexpr e1) (comp_fexpr e2) (comp_fexpr e3) (comp_fexpr e4)
    | S.FSeq e1 e2 => T.FSeq (comp_fexpr e1) (comp_fexpr e2)
    | S.FOut e => T.FOut (comp_fexpr e)
    | S.FArg => T.FArg
    end.

  Definition comp_funmap (fs : S.funmap) : T.funmap :=
    StringMap.map comp_fexpr fs.

  Definition comp_funmap_turn (fs : S.funmap_turn) : T.funmap_turn :=
    StringMap.map (fun '(t, e) => (t, comp_fexpr e)) fs.

  Definition comp_prg (p : prg S.lang) : prg T.lang :=
    T.Build_prg (comp_funmap_turn (S.prg_funs p)) (comp_expr (S.prg_main p)).

  Definition comp_par (p : par S.lang) : par T.lang :=
    T.Build_par (comp_funmap (S.par_funs p)) (comp_expr (S.par_main p)).

  Definition comp_ctx (c : ctx S.lang) : ctx T.lang :=
    T.Build_ctx (comp_funmap (S.ctx_funs c)).

  Definition chain :=
    Build_CompilationChain S.lang T.lang comp_prg comp_par comp_ctx.
End Compiler.

(* Compiler proofs. *)
Module RTCtilde.
  Module S := Source.
  Module T := Target.
  Module C := Compiler.

  (* A simple trace relation that does not track program-context changes. It
     will say less about the target in the source, but also be a bit easier to
     prove. *)
  Definition pub_event (e : T.event) : bool :=
    match e with
    | T.OutputH _ => false
    | T.Output _ | T.Result _ => true
    end.

  Definition clean_event (e : T.event) : S.event :=
    match e with
    | T.Result n => S.Result n
    | T.Output n => S.Output n
    (* Bad case. *)
    | T.OutputH _ => S.Output 0
    end.

  Definition clean_trace (t : T.trace) : S.trace :=
    map clean_event (filter pub_event t). (* Reasoning on filter vs. ... *)

  Inductive trel : S.trace -> T.trace -> Prop :=
  | RelTrace : forall t, T.wf_trace t -> trel (clean_trace t) t.

  (* Properties of trace cleanup. *)
  Remark clean_trace_app : forall t1 t2,
    clean_trace (t1 ++ t2) = clean_trace t1 ++ clean_trace t2.
  Proof.
    induction t1 as [| e t1' IHt1']; intros t2.
    - reflexivity.
    - simpl. unfold clean_trace.
      destruct (pub_event e) eqn:Hcase; simpl; rewrite Hcase; simpl;
        unfold clean_trace in IHt1'; now rewrite IHt1'.
  Qed.

  Remark clean_trace_snoc_result : forall t n,
    clean_trace (t ++ [T.Result n]) = clean_trace t ++ [S.Result n].
  Proof.
    intros; now rewrite clean_trace_app.
  Qed.

  Remark clean_trace_snoc_output : forall t n,
    clean_trace (t ++ [T.Output n]) = clean_trace t ++ [S.Output n].
  Proof.
    intros; now rewrite clean_trace_app.
  Qed.

  Remark clean_trace_snoc_outputh : forall t n,
    clean_trace (t ++ [T.OutputH n]) = clean_trace t.
  Proof.
    intros; rewrite clean_trace_app.
    unfold clean_trace. now rewrite app_nil_r.
  Qed.

  Theorem trel_clean_trace : forall p t,
    T.sem_prg p t ->
    trel (clean_trace t) t.
  Proof.
    intros p t Hsem.
    apply T.sem_trace in Hsem.
    now constructor.
  Qed.

  (* Context cleanup. *)
  Fixpoint clean_expr (e : T.expr) : S.expr :=
    match e with
    | T.Const n => S.Const n
    | T.Plus e1 e2 => S.Plus (clean_expr e1) (clean_expr e2)
    | T.Seq e1 e2 => S.Seq (clean_expr e1) (clean_expr e2)
    | T.OutH e => clean_expr e
    | T.Out e => S.Out (clean_expr e)
    | T.IfLe e1 e2 e3 e4 =>
      S.IfLe (clean_expr e1) (clean_expr e2) (clean_expr e3) (clean_expr e4)
    | T.Fun f e => S.Fun f (clean_expr e)
    end.

  Fixpoint clean_fexpr (e : T.fexpr) : S.fexpr :=
    match e with
    | T.FConst n => S.FConst n
    | T.FPlus e1 e2 => S.FPlus (clean_fexpr e1) (clean_fexpr e2)
    | T.FSeq e1 e2 => S.FSeq (clean_fexpr e1) (clean_fexpr e2)
    | T.FOutH e => clean_fexpr e
    | T.FOut e => S.FOut (clean_fexpr e)
    | T.FIfLe e1 e2 e3 e4 =>
      S.FIfLe (clean_fexpr e1) (clean_fexpr e2) (clean_fexpr e3) (clean_fexpr e4)
    | T.FArg => S.FArg
    end.

  Definition clean_funmap : T.funmap -> S.funmap :=
    StringMap.map clean_fexpr.

  Definition clean_ctx (c : T.ctx) : S.ctx :=
    S.Build_ctx (clean_funmap (T.ctx_funs c)).

  (* Cheat code: the language model does not easily allow a conditional
     formulation based on some well-formedness conditions on program and
     context. Use this to artificially establish that assumed fact after
     program and context have been introduced. *)
  Hypothesis hyp_wf : forall p c, T.prg_wf (T.link (C.comp_par p) c).

  (* Main auxiliary results. *)
  Remark eval_main_link_prg funs_p main_p funs_c main res :
    T.eval_main (T.link_funs (T.Build_par funs_p main_p) (T.Build_ctx funs_c)) main res ->
    let pc := T.Build_prg (T.link_funmaps funs_p funs_c) main in
    T.eval_main (T.prg_funs pc) (T.prg_main pc) res.
  Proof.
    unfold T.link_funs. intros Heval. assumption.
  Qed.

  Remark sem_prg_link funs1 funs2 main t :
    T.sem_prg (T.Build_prg (T.link_funmaps funs1 funs2) main)       t ->
    T.sem_prg (T.link (T.Build_par funs1 main) (T.Build_ctx funs2)) t.
  Proof.
    easy.
  Qed.

  (* If lookup succeeds on a target map containing functions from a compiled
     source program (clean by definition) and a target context, a second lookup
     on the source map containing the functions from the original source program
     and the cleaned functions from the context will also succeed, and its body
     be the body of the first lookup, once cleaned. This property follows
     trivially from our definitions and those of standard maps. *)
  Remark find_clean_ctx : forall k par_s ctx_t tag e,
    StringMap.find k (T.link_funs (C.comp_par par_s)            ctx_t)  = Some (tag, e) ->
    StringMap.find k (S.link_funs             par_s  (clean_ctx ctx_t)) = Some (tag, clean_fexpr e).
  Admitted.

  Lemma eval_fun_clean (arg res : nat) (e : T.fexpr) (t : T.trace) :
    T.eval_fun arg e (res, t) ->
    S.eval_fun arg (clean_fexpr e) (res, clean_trace t).
  Proof.
    revert arg res t.
    induction e; subst;
      intros arg res t Heval;
      inversion Heval; subst;
      simpl.
    - now constructor.
    - rewrite clean_trace_app. constructor.
      + eapply IHe1; eassumption.
      + eapply IHe2; eassumption.
    - rewrite 2!clean_trace_app. econstructor.
      + eapply IHe1; eassumption.
      + eapply IHe2; eassumption.
      + assumption.
      + eapply IHe3; eassumption.
    - rewrite 2!clean_trace_app. eapply S.FEval_IfElse.
      + eapply IHe1; eassumption.
      + eapply IHe2; eassumption.
      + assumption.
      + eapply IHe4; eassumption.
    - rewrite clean_trace_app. eapply S.FEval_Seq.
      + eapply IHe1; eassumption.
      + eapply IHe2; eassumption.
    - rewrite clean_trace_app; simpl. econstructor.
      apply IHe; eassumption.
    - rewrite clean_trace_snoc_outputh.
      apply IHe; assumption.
    - now constructor.
  Qed.

  Ltac t_sem_clean :=
    match goal with
    | IHmain : forall _ _ _ _ , S.sem_prg {| S.prg_funs := _; S.prg_main := ?E |} _,
    Heval_main : T.eval_main _ (C.comp_expr ?E) (_, ?T)
    |- S.eval_main _ ?E (_, clean_trace ?T) =>
      apply eval_main_link_prg in Heval_main;
      pose proof T.Eval_Prg _ _ _ Heval_main as Heval_prg';
      pose proof T.SemEval _ _ Heval_prg' as Hsem_prg';
      apply sem_prg_link in Hsem_prg';
      specialize (IHmain _ _ _ Hsem_prg');
      rewrite clean_trace_snoc_result in IHmain;
      inversion IHmain as [? ? Heval_prg'']; subst;
      inversion Heval_prg'' as [? ? Heval_main'' Htrace]; subst;
      unfold T.link in Heval_main''; simpl in Heval_main'';
      apply app_inj_tail in Htrace as [Ht Hn]; inversion Hn; subst;
      eassumption
  end.

  Theorem sem_clean (par_s : S.par) (ctx_t : T.ctx) (t : T.trace) :
    T.sem_prg (T.link (C.comp_par par_s) ctx_t) t ->
    S.sem_prg (S.link par_s (clean_ctx ctx_t)) (clean_trace t).
  Proof.
    unfold S.link, T.link.
    set (Hpar_s := par_s). destruct par_s as [funs_s main_s].
    set (Hctx_t := ctx_t). destruct ctx_t as [funs_t].
    simpl.
    revert funs_s Hpar_s funs_t Hctx_t t.
    (* Induction on the main expression. *)
    induction main_s;
      intros funs_s Hpar_s funs_t Hctx_t t Hsem;
      simpl in *.
    - (* Const. *)
      inversion Hsem as [? ? Heval_prg]; subst.
      inversion Heval_prg as [? ? Heval_main]; subst.
      inversion Heval_main; subst.
      simpl in *.
      unfold clean_trace. simpl. change [S.Result ?X] with ([] ++ [S.Result X]).
      now do 3 constructor.
    - (* Plus. *)
      inversion Hsem as [? ? Heval_prg]; subst.
      inversion Heval_prg as [? ? Heval_main]; subst.
      inversion Heval_main; subst.
      simpl in *.
      rewrite clean_trace_snoc_result, clean_trace_app.
      do 3 constructor;
        now t_sem_clean.
    - (* If. *)
      inversion Hsem as [? ? Heval]; subst.
      inversion Heval as [m l Heval']; subst. simpl in Heval'.
      inversion Heval'; subst;
        rewrite clean_trace_snoc_result, 2!clean_trace_app;
        do 2 econstructor.
      + (* Then branch. *)
        eapply S.Eval_IfThen; try eassumption;
          now t_sem_clean.
      + (* Else branch. *)
        eapply S.Eval_IfElse; try eassumption;
          now t_sem_clean.
    - (* Seq. *)
      inversion Hsem as [? ? Heval_prg]; subst.
      inversion Heval_prg as [? ? Heval_main]; subst.
      inversion Heval_main; subst.
      simpl in *.
      rewrite clean_trace_snoc_result, clean_trace_app.
      do 3 econstructor;
        now t_sem_clean.
    - (* Out. *)
      inversion Hsem as [? ? Heval_prg]; subst.
      inversion Heval_prg as [? ? Heval_main]; subst.
      inversion Heval_main; subst.
      simpl in *.
      rewrite clean_trace_snoc_result, clean_trace_snoc_output.
      do 3 constructor.
      now t_sem_clean.
    - (* Fun. *)
      inversion Hsem as [? ? Heval]; subst.
      inversion Heval as [m l Heval']; subst. simpl in Heval'.
      inversion Heval'; subst;
        rewrite clean_trace_snoc_result;
        do 2 constructor.
      + (* Found *)
        rewrite clean_trace_app. econstructor.
        * apply find_clean_ctx in H3. eassumption.
        * (* Standard inductive case (on an existential and other names). *)
          now t_sem_clean.
        * eapply eval_fun_clean; last eassumption.
      + (* Not found: contradiction based on well-formedness assumption. *)
        pose proof hyp_wf Hpar_s Hctx_t as Hwf.
        inversion Hwf as [| | | | | | ? ? Hcontra]; subst.
        unfold T.link, Hpar_s, Hctx_t in Hcontra. simpl in Hcontra.
        apply StringMap.mem_2 in Hcontra.
        apply StringMapFacts.not_find_in_iff in H0.
        contradiction.
  Qed.

  (* Main theorem. *)
  Corollary extra_target_RTCt : rel_RTC C.chain S.sem T.sem trel.
  Proof.
    unfold rel_RTC. simpl. intros par_s ctx_t t Hsem.
    exists (clean_ctx ctx_t), (clean_trace t). split.
    - eapply trel_clean_trace; eassumption.
    - now apply sem_clean.
  Qed.
End RTCtilde.
