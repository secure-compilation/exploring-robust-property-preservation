Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.FSets.FMapInterface.
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

(* And function name sets, for interfacing purposes. *)
Module StringSet := FSetWeakList.Make DecidableString.
Notation "∅" := StringSet.empty (at level 70, no associativity).
Notation "s1 ∪ s2" := (StringSet.union s1 s2) (at level 70, right associativity).

Definition elements_set (A : Type) (m : StringMap.t A) : StringSet.t :=
  let keys := map fst (StringMap.elements m) in
  fold_left (fun acc key => StringSet.add key acc) keys StringSet.empty.

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
    }.

  Record ctx :=
    {
      ctx_funs : funmap;
      ctx_main : expr;
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

  (* Linking. Assume main in the program and combine functions from program and
     context with tags to remember provenance. *)
  Definition link_fun (par_fun ctx_fun : option fexpr) :=
    match par_fun, ctx_fun with
    | Some f, _ => Some (ProgramTurn, f)
    | _, Some f => Some (ContextTurn, f)
    | _, _ => None
    end.

  Definition link_funs (p : par) (c : ctx) :=
    StringMap.map2 link_fun (par_funs p) (ctx_funs c).

  (* Lemma link_wf  (p : par) (c : ctx) : *)
  (*   closed (link_funs p c) (par_main p) = true -> *)
  (*   par_wf (par_funs p) (par_main p) -> *)
  (*   ctx_wf (ctx_funs c) -> *)
  (*   prg_wf (link_funs p c) (par_main p). *)
  (* Admitted. *)

  Definition link (p : par) (c : ctx) : prg :=
    Build_prg (link_funs p c) (ctx_main c).

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

  Remark trace_exists : forall W : prg, exists t : trace, sem_prg W t.
  Admitted.

  Inductive wf_trace : trace -> Prop :=
  | WFTrace : forall t t' res,
      t = t' ++ [Result res] -> Forall reg_event t' -> wf_trace t.

  Theorem sem_trace : forall p t, sem_prg p t -> wf_trace t.
  Admitted.

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
    }.

  Record ctx :=
    {
      ctx_funs : funmap;
      ctx_main : expr;
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

  (* Linking. Assume main in the program and combine functions from program and
     context with tags to remember provenance. *)
  Definition link_fun (par_fun ctx_fun : option fexpr) :=
    match par_fun, ctx_fun with
    | Some f, _ => Some (ProgramTurn, f)
    | _, Some f => Some (ContextTurn, f)
    | _, _ => None
    end.

  Definition link_funs (p : par) (c : ctx) :=
    StringMap.map2 link_fun (par_funs p) (ctx_funs c).

  (* Lemma link_wf  (p : par) (c : ctx) : *)
  (*   closed (link_funs p c) (par_main p) = true -> *)
  (*   par_wf (par_funs p) (par_main p) -> *)
  (*   ctx_wf (ctx_funs c) -> *)
  (*   prg_wf (link_funs p c) (par_main p). *)
  (* Admitted. *)

  Definition link (p : par) (c : ctx) : prg :=
    Build_prg (link_funs p c) (ctx_main c).

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

  Remark trace_exists : forall W : prg, exists t : trace, sem_prg W t.
  Admitted.

  Inductive wf_trace : trace -> Prop :=
  | WFTrace : forall t t' res,
      t = t' ++ [Result res] -> Forall reg_event t' -> wf_trace t.

  Theorem sem_trace : forall p t, sem_prg p t -> wf_trace t.
  Admitted.

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
    T.Build_par (comp_funmap (S.par_funs p)).

  Definition comp_ctx (c : ctx S.lang) : ctx T.lang :=
    T.Build_ctx (comp_funmap (S.ctx_funs c)) (comp_expr (S.ctx_main c)).

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
  Theorem trel_clean_trace : forall p t,
    T.sem_prg p t ->
    trel (clean_trace t) t.
  Admitted.

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

  Definition clean_funmap : T.funmap ->S.funmap :=
    StringMap.map clean_fexpr.

  Definition clean_ctx (c : T.ctx) : S.ctx :=
    S.Build_ctx (clean_funmap (T.ctx_funs c)) (clean_expr (T.ctx_main c)).

  (* Main auxiliary results. *)
  Theorem sem_clean (par_s : S.par) (ctx_t : T.ctx) (t : T.trace) :
    T.sem_prg (T.link (C.comp_par par_s) ctx_t) t ->
    S.sem_prg (S.link par_s (clean_ctx ctx_t)) (clean_trace t).
  Admitted.

  (* Main theorem. *)
  Corollary extra_target_RTCt : rel_RTC C.chain S.sem T.sem trel.
  Proof.
    unfold rel_RTC. simpl. intros par_s ctx_t t Hsem.
    exists (clean_ctx ctx_t), (clean_trace t). split.
    - eapply trel_clean_trace; eassumption.
    - now apply sem_clean.
  Qed.
End RTCtilde.
