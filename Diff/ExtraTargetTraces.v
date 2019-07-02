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

(* Shared core of source and target languages. For reuse, it seems easiest that
   they assemble the following components only very slightly differently. *)
Module Core.
  (* Base expressions.
       RB: An observable effect sequenced with a follow-up expression is added to
     the core and allowed selectively. Without let bindings, this is not very
     convenient to use, but suffices for a first approximation.
       It seems reasonable to treat functions (name and argument) at this level
     rather than separately. Local restrictions need to be enforced anyway, so
     a separate level makes little difference.
       One can abuse Coq's computational mechanism to an extent, but not to the
     point that the semantics cannot see (relevant) function calls. *)
  Inductive expr : Type :=
  | Const : nat -> expr
  | Plus  : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | IfLe  : expr -> expr -> expr -> expr -> expr
  | Out   : expr -> expr -> expr
  | Fun   : StringMap.key -> expr -> expr
  | Arg   : expr.

  (* Function types.
       RB: Well-formedness conditions are at the moment basically restrictions on
     functions.
      - For the sake of simplicity, functions are not allowed to call other
        functions. (When they do, start by avoiding recursivity.)
      - Functions take singleton arguments (enforced syntactically). Further,
        argument references may not appear in main expressions.
      - Function bodies are otherwise simple expressions, where the argument has
        its reserved, special meaning. *)
  Definition funmap := StringMap.t expr.
  Definition funmap_turn := StringMap.t (turn * expr).
  Definition funset := StringSet.t.

  (* Structural properties of expressions. *)
  Inductive funless : expr -> Prop :=
  | FunlessConst : forall n,
      funless (Const n)
  | FunlessPlus : forall e1 e2,
      funless e1 -> funless e2 -> funless (Plus e1 e2)
  | FunlessTimes : forall e1 e2,
      funless e1 -> funless e2 -> funless (Times e1 e2)
  | FunlessIfLe : forall econd1 econd2 ethen eelse,
      funless econd1 -> funless econd2 -> funless ethen -> funless eelse ->
      funless (IfLe econd1 econd2 ethen eelse)
  | FunlessOut : forall eout e,
      funless eout -> funless e -> funless (Out eout e)
  | FunlessArg :
      funless Arg.

  Inductive argless : expr -> Prop :=
  | ArglessConst : forall n,
      argless (Const n)
  | ArglessPlus : forall e1 e2,
      argless e1 -> argless e2 -> argless (Plus e1 e2)
  | ArglessTimes : forall e1 e2,
      argless e1 -> argless e2 -> argless (Times e1 e2)
  | ArglessIfLe : forall econd1 econd2 ethen eelse,
      argless econd1 -> argless econd2 -> argless ethen -> argless eelse ->
      argless (IfLe econd1 econd2 ethen eelse)
  | ArglessOut : forall eout e,
      argless eout -> argless e -> argless (Out eout e)
  | ArglessFun id earg :
      argless earg -> argless (Fun id earg).

  (* Some additional helpers to write properties. *)
  Definition funmap_bodies (fs : funmap) : list expr :=
    List.map snd (StringMap.elements fs).

  Definition funmap_funless (fs : funmap) : Prop :=
    Forall funless (funmap_bodies fs).

  Definition funmap_turn_bodies (fs : funmap_turn) : funmap :=
    StringMap.map snd fs.

  Inductive well_formed_calls (fs : funmap_turn) : expr -> Prop :=
  | CallsConst : forall n,
      well_formed_calls fs (Const n)
  | CallsPlus : forall e1 e2,
      well_formed_calls fs e1 -> well_formed_calls fs e2 ->
      well_formed_calls fs (Plus e1 e2)
  | CallsTimes : forall e1 e2,
      well_formed_calls fs e1 -> well_formed_calls fs e2 ->
      well_formed_calls fs (Times e1 e2)
  | CallsIfLe : forall econd1 econd2 ethen eelse,
      well_formed_calls fs econd1 -> well_formed_calls fs econd2 ->
      well_formed_calls fs ethen -> well_formed_calls fs eelse ->
      well_formed_calls fs (IfLe econd1 econd2 ethen eelse)
  | CallsOut : forall eout e,
      well_formed_calls fs eout -> well_formed_calls fs e ->
      well_formed_calls fs (Out eout e)
  | CallsFun id earg :
      StringMap.mem id fs = true ->
      well_formed_calls fs earg -> well_formed_calls fs (Fun id earg)
  | CallsArg :
      well_formed_calls fs Arg.

  (* A simple notion of closed program with implicit, exact interfaces. *)
  Fixpoint funs (e : expr) : funset :=
    match e with
    | Const _ | Arg => ∅
    | Plus e1 e2 | Times e1 e2 | Out e1 e2 => funs e1 ∪ funs e2
    | IfLe e1 e2 e3 e4 => funs e1 ∪ funs e2 ∪ funs e3 ∪ funs e3
    | Fun f e => StringSet.add f (funs e)
    end.

  Definition closed (fs : funmap_turn) (e : expr) : bool :=
    StringSet.equal (elements_set _ fs) (funs e).

  (* Programs and contexts with their well-formedness conditions.
       RB: Morally, this places everything (back, except maps for the use of
     stdlib maps) in Set. *)
  Record par_wf (funs : funmap) (main : expr) :=
    {
      par_wf_funless : funmap_funless funs;
      par_wf_argless : argless main
    }.

  Record par :=
    {
      par_funs : funmap;
      par_main : expr;
      (* par_prop : par_wf par_funs par_main *)
    }.

  Record ctx_wf (funs : funmap) :=
    {
      ctx_wf_funless : funmap_funless funs
    }.

  Record ctx :=
    {
      ctx_funs : funmap;
      (* ctx_prop : ctx_wf ctx_funs *)
    }.

  Record prg_wf (funs : funmap_turn) (main : expr) :=
    {
      prg_wf_funless : funmap_funless (funmap_turn_bodies funs);
      prg_wf_argless : argless main;
      prg_wf_calls : well_formed_calls funs main
    }.

  Record prg :=
    {
      prg_funs : funmap_turn;
      prg_main : expr;
      (* prg_prop : prg_wf prg_funs prg_main *)
    }.

  (* Linking. Assume main in the program and combine functions from program and
     context with tags to remember provenance.
       RB: Clashes are resolved by favoring the program side, but should never
     be allowed. (Inline auxiliaries?) *)

  (* First, trivially, consider the case of the empty program. *)
  Lemma wf_empty_prg : prg_wf (StringMap.empty _) (Const 0).
  Admitted.

  Definition empty_prg : prg :=
    Build_prg
      (StringMap.empty _)
      (Const 0)
      (* wf_empty_prg *)
  .

  (* Second, compose proper well-formedness proofs. *)
  Definition link_fun (par_fun ctx_fun : option expr) :=
    match par_fun, ctx_fun with
    | Some f, _ => Some (ProgramTurn, f)
    | _, Some f => Some (ContextTurn, f)
    | _, _ => None
    end.

  Definition link_funmaps (funs_p funs_c : funmap) : funmap_turn :=
    StringMap.map2 link_fun funs_p funs_c.

  Definition link_funs (p : par) (c : ctx) : funmap_turn :=
    link_funmaps  (par_funs p) (ctx_funs c).

  Remark link_funs_main : forall funs_p funs_c main_p main_p',
      link_funs (Build_par funs_p main_p ) (Build_ctx funs_c) =
      link_funs (Build_par funs_p main_p') (Build_ctx funs_c).
  Proof.
    unfold link_funs. reflexivity.
  Qed.

  Definition linkable (p : par) (c : ctx) : bool :=
    closed (link_funs p c) (par_main p).

  Lemma link_wf (p : par) (c : ctx) :
    linkable p c = true ->
    par_wf (par_funs p) (par_main p) ->
    ctx_wf (ctx_funs c) ->
    prg_wf (link_funs p c) (par_main p).
  Admitted.

  Definition link_opt (p : par) (c : ctx) (*Hlinkable : linkable p c = true*) : option prg :=
    if linkable p c
    then Some (Build_prg (link_funs p c) (par_main p))
    else None.

  Theorem link_ok :
    forall p c, linkable p c = true ->
    exists pc, link_opt p c = Some pc.
  Proof.
    intros p c Hlinkable. eexists.
    unfold link_opt. rewrite Hlinkable. reflexivity.
  Qed.

  Definition link (p : par) (c : ctx) : prg :=
    Build_prg (link_funs p c) (par_main p).

  (* Traces as evaluation results. *)
  Inductive event : Set :=
  | Result : nat -> event
  | Output : nat -> event.

  Definition trace := list event.

  (* Evaluation-based semantics, returns both trace and result.
       RB: An Out expression can itself produce traces, which is nonstandard.
     Should it?
       RB: Rename to eval?
       RB: Currently no program-context switching information recorded.
       RB: Also currently, getting away with two simple but mostly redundant
     fixpoints. *)
  (* Definition eval_fun (arg : nat) (e : expr) : (nat * list nat) := *)
  (*   let fix eval e := *)
  (*       match e with *)
  (*       | Const n => (n, []) *)
  (*       | Plus e1 e2 => *)
  (*         match eval e1, eval e2 with *)
  (*         | (n1, t1), (n2, t2) => (n1 + n2, t1 ++ t2) *)
  (*         end *)
  (*       | Times e1 e2 => *)
  (*         match eval e1, eval e2 with *)
  (*         | (n1, t1), (n2, t2) => (n1 * n2, t1 ++ t2) *)
  (*         end *)
  (*       | IfLe ecomp1 ecomp2 ethen eelse => *)
  (*         match eval ecomp1, eval ecomp2 with *)
  (*         | (n1, t1), (n2, t2) => *)
  (*           if n1 <=? n2 *)
  (*           then let '(n, t) := eval ethen in (n, t1 ++ t2 ++ t) *)
  (*           else let '(n, t) := eval eelse in (n, t1 ++ t2 ++ t) *)
  (*         end *)
  (*       | Out eout e' => *)
  (*         match eval eout, eval e' with *)
  (*         | (nout, tout), (n, t) => (n, tout ++ [nout] ++ t) *)
  (*         end *)
  (*       | Fun id earg => (0, []) (* Bad case, rule out in closed programs. *) *)
  (*       | Arg => (arg, []) *)
  (*       end *)
  (*   in eval e. *)

  Inductive eval_fun (arg : nat) : expr -> (nat * trace) -> Prop :=
  | FEval_Const : forall n,
      eval_fun arg (Const n) (n, [])
  | FEval_Plus : forall e1 e2 n1 n2 t1 t2,
      eval_fun arg e1 (n1, t1) -> eval_fun arg e2 (n2, t2) ->
      eval_fun arg (Plus e1 e2) (n1 + n2, t1 ++ t2)
  | FEval_Times : forall e1 e2 n1 n2 t1 t2,
      eval_fun arg e1 (n1, t1) -> eval_fun arg e2 (n2, t2) ->
      eval_fun arg (Times e1 e2) (n1 * n2, t1 ++ t2)
  | FEval_IfThen : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_fun arg ecomp1 (n1, t1) -> eval_fun arg ecomp2 (n2, t2) ->
      n1 <= n2 -> eval_fun arg ethen (n, t) ->
      eval_fun arg (IfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | FEval_IfElse : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_fun arg ecomp1 (n1, t1) -> eval_fun arg ecomp2 (n2, t2) ->
      n1 > n2 -> eval_fun arg eelse (n, t) ->
      eval_fun arg (IfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | FEval_Out : forall eout e nout n tout t,
      eval_fun arg eout (nout, tout) -> eval_fun arg e (n, t) ->
      eval_fun arg (Out eout e) (n, tout ++ [Output nout] ++ t)
  | FEval_Arg :
      eval_fun arg Arg (arg, [])
  (* A temporary hack covering the bad case. *)
  | FEval_BadFun : forall id earg,
      eval_fun arg (Fun id earg) (0, []).

  (* Definition eval_main (fs : funmap_turn) (e : expr) : (nat * list nat) := *)
  (*   let fix eval e := *)
  (*       match e with *)
  (*       | Const n => (n, []) *)
  (*       | Plus e1 e2 => *)
  (*         match eval e1, eval e2 with *)
  (*         | (n1, t1), (n2, t2) => (n1 + n2, t1 ++ t2) *)
  (*         end *)
  (*       | Times e1 e2 => *)
  (*         match eval e1, eval e2 with *)
  (*         | (n1, t1), (n2, t2) => (n1 * n2, t1 ++ t2) *)
  (*         end *)
  (*       | IfLe ecomp1 ecomp2 ethen eelse => *)
  (*         match eval ecomp1, eval ecomp2 with *)
  (*         | (n1, t1), (n2, t2) => *)
  (*           if n1 <=? n2 *)
  (*           then let '(n, t) := eval ethen in (n, t1 ++ t2 ++ t) *)
  (*           else let '(n, t) := eval eelse in (n, t1 ++ t2 ++ t) *)
  (*         end *)
  (*       | Out eout e' => *)
  (*         match eval eout, eval e' with *)
  (*         | (nout, tout), (n, t) => (n, tout ++ [nout] ++ t) *)
  (*         end *)
  (*       | Fun id earg => *)
  (*         let '(arg, targ) := eval earg in *)
  (*         match StringMap.find id fs with *)
  (*         | Some (_, e') => *)
  (*           let '(n, t) := eval_fun arg e' in *)
  (*           (n, targ ++ t) *)
  (*         | None => (0, []) (* Bad case, rule out in closed programs. *) *)
  (*         end *)
  (*       | Arg => (0, []) (* Bad case, ruled out by main. *) *)
  (*       end *)
  (*   in eval e. *)

  Inductive eval_main (fs : funmap_turn) : expr -> (nat * trace) -> Prop :=
  | Eval_Const : forall n,
      eval_main fs (Const n) (n, [])
  | Eval_Plus : forall e1 e2 n1 n2 t1 t2,
      eval_main fs e1 (n1, t1) -> eval_main fs e2 (n2, t2) ->
      eval_main fs (Plus e1 e2) (n1 + n2, t1 ++ t2)
  | Eval_Times : forall e1 e2 n1 n2 t1 t2,
      eval_main fs e1 (n1, t1) -> eval_main fs e2 (n2, t2) ->
      eval_main fs (Times e1 e2) (n1 * n2, t1 ++ t2)
  | Eval_IfThen : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_main fs ecomp1 (n1, t1) -> eval_main fs ecomp2 (n2, t2) ->
      n1 <= n2 -> eval_main fs ethen (n, t) ->
      eval_main fs (IfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | Eval_IfElse : forall ecomp1 ecomp2 ethen eelse n1 n2 n t1 t2 t,
      eval_main fs ecomp1 (n1, t1) -> eval_main fs ecomp2 (n2, t2) ->
      n1 > n2 -> eval_main fs eelse (n, t) ->
      eval_main fs (IfLe ecomp1 ecomp2 ethen eelse) (n, t1 ++ t2 ++ t)
  | Eval_Out : forall eout e nout n tout t,
      eval_main fs eout (nout, tout) -> eval_main fs e (n, t) ->
      eval_main fs (Out eout e) (n, tout ++ [Output nout] ++ t)
  | Eval_Fun : forall id turn earg e arg n targ t,
      StringMap.find id fs = Some (turn, e) ->
      eval_main fs earg (arg, targ) -> eval_fun arg e (n, t) ->
      eval_main fs (Fun id earg) (n, targ ++ t)
  (* Two temporary hacks covering the bad cases. Without self-contained
     well-formedness conditions in the programs, additional hypotheses are
     required to discard them. *)
  | Eval_BadFun : forall id earg,
      StringMap.find id fs = None ->
      eval_main fs (Fun id earg) (0, [])
  | Eval_BadArg :
      eval_main fs Arg (0, []).

  Inductive eval_prg (p : prg) : trace -> Prop :=
  | Eval_Prg : forall n t,
      eval_main (prg_funs p) (prg_main p) (n, t) ->
      eval_prg p (t ++ [Result n]).

  Inductive sem : prg -> trace -> Prop :=
  | SemEval : forall p t, eval_prg p t -> sem p t.

  Remark trace_exists : forall W : prg, exists t : trace, sem W t.
  Proof.
    intros [funs main].
    induction main.
    - eexists. now do 3 econstructor.
  Admitted.

  Remark eval_main_link_prg funs_p main_p funs_c main res :
    eval_main (link_funs (Build_par funs_p main_p) (Build_ctx funs_c)) main res ->
    let pc := Build_prg (link_funmaps funs_p funs_c) main in
    eval_main (prg_funs pc) (prg_main pc) res.
  Proof.
    unfold link_funs. intros Heval. assumption.
  Qed.
End Core.

(* Target language. *)
Module Target.
  (* The target language is simply the full, unadulterated core. *)
  Definition lang := Build_Language Core.link.
  Definition sem := Build_Semantics lang Core.sem Core.trace_exists.
End Target.

(* Source language. *)
Module Source.
  (* A series of inductive definitions describing the absence of Out statements.
     In expressions, symbolic function calls say nothing about the function
     definitions proper. *)
  Inductive outless_expr : Core.expr -> Prop :=
  | OutlessConst : forall n,
      outless_expr (Core.Const n)
  | OutlessPlus : forall e1 e2,
      outless_expr e1 -> outless_expr e2 -> outless_expr (Core.Plus e1 e2)
  | OutlessTimes : forall e1 e2,
      outless_expr e1 -> outless_expr e2 -> outless_expr (Core.Times e1 e2)
  | OutlessIfLe : forall econd1 econd2 ethen eelse,
      outless_expr econd1 -> outless_expr econd2 ->
      outless_expr ethen -> outless_expr eelse ->
      outless_expr (Core.IfLe econd1 econd2 ethen eelse)
  | OutlessFun : forall id earg,
      outless_expr earg -> outless_expr (Core.Fun id earg).

  Definition funmap_outless (fs : Core.funmap) : Prop :=
    Forall outless_expr (Core.funmap_bodies fs).

  (* Decorate core programs with their additional property. *)
  Record par_wf (p : Core.par) :=
    {
      par_wf_funs_outless : funmap_outless (Core.par_funs p);
      par_wf_main_outless : outless_expr (Core.par_main p)
    }.

  Record par :=
    {
      par_core : Core.par;
      (* par_prop : par_wf par_core *)
    }.

  Record ctx_wf (c : Core.ctx) :=
    {
      ctx_wf_funs_outless : funmap_outless (Core.ctx_funs c);
    }.

  Record ctx :=
    {
      ctx_core : Core.ctx;
      (* ctx_prop : ctx_wf ctx_core *)
    }.

  Record prg_wf (p : Core.prg) :=
    {
      prg_wf_funs_outless :
        funmap_outless (Core.funmap_turn_bodies (Core.prg_funs p));
      prg_wf_main_outless : outless_expr (Core.prg_main p)
    }.

  Record prg :=
    {
      prg_core : Core.prg;
      (* prg_prop : prg_wf prg_core *)
    }.

  (* Wrap link operation and define language. *)
  (* Lemma link_wf (p : par) (c : ctx) : *)
  (*   par_wf (par_core p) -> *)
  (*   ctx_wf (ctx_core c) -> *)
  (*   prg_wf (Core.link (par_core p) (ctx_core c)). *)
  (* Admitted. *)

  Definition linkable (p : par) (c : ctx) : bool :=
    Core.linkable (par_core p) (ctx_core c).

  Definition link_opt (p : par) (c : ctx) : option prg :=
    match Core.link_opt (par_core p) (ctx_core c) with
    | Some pc => Some (Build_prg pc)
    | None => None
    end.

  Theorem link_ok :
    forall p c, linkable p c = true ->
    exists pc, link_opt p c = Some pc.
  Proof.
    unfold linkable, link_opt.
    intros p c Hlinkable.
    unfold linkable in Hlinkable.
    apply Core.link_ok in Hlinkable as [pc Hlinkable].
    eexists. rewrite Hlinkable. reflexivity.
  Qed.

  Definition link (p : par) (c : ctx) : prg :=
    Build_prg (Core.link (par_core p) (ctx_core c)).

  Definition empty_prg := Build_prg Core.empty_prg.

  Definition lang := Build_Language link.

  (* Wrap core and define semantics. *)
  Definition sem_wrap (p : prg) : Core.trace -> Prop := Core.sem (prg_core p).

  Remark trace_exists : forall W : prg, exists t : Core.trace, sem_wrap W t.
  Admitted.

  Definition sem := Build_Semantics lang sem_wrap trace_exists.
End Source.

(* Compiler. *)
Module Compiler.
  (* Build the identity compiler from the shared core and define the chain.
       Observe that this transformation amounts to stripping off the extra,
     source-only properties stating the absence of Out commands and their
     associated events. *)
  Definition comp_prg (p : prg Source.lang) : prg Target.lang := Source.prg_core p.
  Definition comp_par (p : par Source.lang) : par Target.lang := Source.par_core p.
  Definition comp_ctx (c : ctx Source.lang) : ctx Target.lang := Source.ctx_core c.

  Definition chain :=
    Build_CompilationChain Source.lang Target.lang comp_prg comp_par comp_ctx.
End Compiler.

(* Compiler proofs. *)
Module RTCtilde.
  (* Work takes place in the core language, so make this implicit. *)
  Import Core.

  (* Well-formedness of programs as assumptions. This works around some
     imperfections in the common definitions but is potentially inconsistent,
     and must be applied judiciously. *)
  Parameter wf_par_c : forall p, Core.par_wf (Core.par_funs p) (Core.par_main p).
  Parameter wf_ctx_c : forall c, Core.ctx_wf (Core.ctx_funs c).
  Parameter wf_prg_c : forall p, Core.prg_wf (Core.prg_funs p) (Core.prg_main p).
  Parameter wf_par_s : forall p, Source.par_wf p.
  Parameter wf_ctx_s : forall c, Source.ctx_wf c.
  Parameter wf_prg_s : forall p, Source.prg_wf p.

  (* A simple trace relation that does not track program-context changes. It
     will say less about the target in the source, but also be a bit easier to
     prove. *)
  Inductive trel : trace -> trace -> Prop :=
  | RelResult : forall n,
      trel [Result n] [Result n]
  | RelOutput : forall ns nt t,
      trel [Result ns] t -> trel [Result ns] (Output nt :: t).

  (* Clean up contexts and traces.
       RB: Better names to avoid Core vs. Target and Source confusion. *)
  Fixpoint clean_expr (e : expr) : expr :=
    match e with
    | Const _ | Arg => e
    | Plus e1 e2 => Plus (clean_expr e1) (clean_expr e2)
    | Times e1 e2 => Times (clean_expr e1) (clean_expr e2)
    | Out _ e' => clean_expr e'
    | IfLe econd1 econd2 ethen eelse =>
      IfLe (clean_expr econd1) (clean_expr econd2)
                (clean_expr ethen) (clean_expr eelse)
    | Fun f e' => Fun f (clean_expr e')
    end.

  Lemma core_ctx_wf_clean_expr (ctx : ctx) :
    ctx_wf (ctx_funs ctx) ->
    ctx_wf (StringMap.map clean_expr (ctx_funs ctx)).
  Admitted.

  Definition clean_ctx_core (ctx : ctx) :=
    Build_ctx
       (StringMap.map clean_expr (ctx_funs ctx))
       (* (core_ctx_wf_clean_expr _ (ctx_prop ctx))) *)
  .

  Lemma source_ctx_wf_clean_expr (ctx : ctx) :
    Source.ctx_wf (clean_ctx_core ctx).
  Admitted.

  Definition clean_ctx (ctx : ctx) : Source.ctx :=
    Source.Build_ctx
      (clean_ctx_core ctx)
      (* (source_ctx_wf_clean_expr _) *)
  .

  (* Fixpoint clean_trace (t : trace) : trace := *)
  (*   match t with *)
  (*   | Result n => t *)
  (*   | Output n t' => clean_trace t' *)
  (*   end. *)
  Definition clean_trace (t : trace) : trace :=
    [last t (Result 0)]. (* Ensure default is never used. *)

  (* Properties of trace cleanup. *)
  Remark last_cons_singleton : forall A (l : list A) a d, last (l ++ [a]) d = a.
  Admitted.

  Remark clean_trace_some_result :
    forall p t, sem p t ->
    exists n, clean_trace t = [Result n].
  Proof.
    intros p t Hsem.
    inversion Hsem as [? ? Heval]; subst.
    inversion Heval as [n t' Heval']; subst.
    exists n. unfold clean_trace.
    destruct t' as [n' | n' t'].
    - reflexivity.
    - now rewrite last_cons_singleton.
  Qed.

  Remark clean_trace_last_result : forall p t n,
    sem p (t ++ [Result n]) ->
    clean_trace (t ++ [Result n]) = [Result n].
  Proof.
    intros p t n Hsem.
    unfold clean_trace. now rewrite last_cons_singleton.
  Qed.

  (* Lemma trel_clean_trace : forall t, trel (clean_trace t) t. *)
  (* Proof. *)
  (*   intros t. induction t as [| n t IHt]. *)
  (*   - now constructor. *)
  (*   - simpl. destruct (clean_trace_result t) as [n' Hclean]. *)
  (*     rewrite Hclean in *. now constructor. *)
  (* Qed. *)

  (* Properties of context cleanup. *)
  Lemma wf_clean_ctx :
    forall ctx, Source.ctx_wf (Source.ctx_core (clean_ctx ctx)).
  Admitted.

  Lemma find_clean_ctx : forall k par_s ctx_t tag e,
    StringMap.find k (link_funs par_s ctx_t) = Some (tag, e) ->
    StringMap.find k (link_funs par_s (clean_ctx_core ctx_t)) = Some (tag, clean_expr e).
  Admitted.

  (* Main auxiliary results. *)
  Lemma eval_fun_clean (arg res : nat) (e : expr) (t : trace) :
    funless e ->
    eval_fun arg e (res, t) ->
    eval_fun arg (clean_expr e) (res, []).
  Proof.
    revert arg res t.
    induction e; subst;
      intros arg res t Hwf Heval;
      inversion Hwf; subst;
      inversion Heval; subst;
      simpl.
    - assumption.
    - change [] with (@nil event ++ []). constructor.
      + eapply IHe1; eassumption.
      + eapply IHe2; eassumption.
    - change [] with (@nil event ++ []). constructor.
      + eapply IHe1; eassumption.
      + eapply IHe2; eassumption.
    - change [] with (@nil event ++ [] ++ []). econstructor.
      + eapply IHe1; eassumption.
      + eapply IHe2; eassumption.
      + assumption.
      + eapply IHe3; eassumption.
    - change [] with (@nil event ++ [] ++ []). eapply FEval_IfElse.
      + eapply IHe1; eassumption.
      + eapply IHe2; eassumption.
      + assumption.
      + eapply IHe4; eassumption.
    - eapply IHe2; eassumption.
    - assumption.
  Qed.

  Lemma sem_clean (par_s : Source.par) (ctx_t : Core.ctx) (t : trace) :
    Core.sem (Core.link (Compiler.comp_par par_s) ctx_t) t ->
    Source.sem_wrap (Source.link par_s (clean_ctx ctx_t)) (clean_trace t).
  Proof.
    (* Initial well-formedness conditions -- because of the simple setting and
       the various harmonies, these are not currently as necessary as they would
       generally be. *)
    (* pose proof wf_par_s (Source.par_core par_s) as Hwf_par_s. *)
    (* pose proof wf_ctx_t ctx_t as Hwf_ctx_t. *)
    (* Some syntactic manipulations. *)
    destruct par_s as [par_s].
    unfold Source.sem_wrap, Source.link,
           Source.prg_core, Source.par_core, Source.ctx_core;
           (* link, link_funs; *)
      simpl;
      intros Hsem.
    set (Hpar_s := par_s).
    set (Hctx_t := ctx_t).
    remember (par_main par_s) as main eqn:Hmain.
    (* Induction on the main expression. *)
    revert par_s Hpar_s ctx_t Hctx_t t Hsem Hmain.
    induction main;
      intros par_s Hpar_s ctx_t Hctx_t t Hsem Hmain;
      destruct par_s as [funs_s main_s];
      destruct ctx_t as [funs_t];
      simpl in *; subst.
    - (* Const *)
      inversion Hsem as [? ? Heval]; subst.
      inversion Heval as [m l Heval']; subst. simpl in Heval'.
      constructor. unfold clean_trace. rewrite last_cons_singleton.
      inversion Heval'; subst.
      change [Result m] with (nil ++ [Result m]). constructor. simpl.
      now constructor.
    - (* Plus *)
      inversion Hsem as [? ? Heval]; subst.
      inversion Heval as [m l Heval']; subst. simpl in Heval'.
      constructor. unfold clean_trace. rewrite last_cons_singleton.
      inversion Heval'; subst.
      change [Result (n1 + n2)] with (nil ++ [Result (n1 + n2)]). constructor. simpl.
      change [] with (@nil event ++ []). constructor.
      + apply eval_main_link_prg in H2.
        pose proof Eval_Prg _ _ _ H2 as Heval1.
        pose proof SemEval _ _ Heval1 as Hsem1.
        assert (Hsem1' : sem (link (Build_par funs_s main1) (Build_ctx funs_t)) (t1 ++ [Result n1]))
          by admit.
        specialize (IHmain1 _ _ _ Hsem1' (eq_refl _)).
        unfold clean_trace in IHmain1. rewrite last_cons_singleton in IHmain1.
        inversion IHmain1 as [? ? Heval1']; subst.
        inversion Heval1' as [? ? Heval1'' Htrace]; subst.
        unfold link in Heval1''. simpl in Heval1''.
        change [Result n1] with ([] ++ [Result n1]) in Htrace.
        apply app_inj_tail in Htrace as [Ht Hn]; inversion Hn; subst n t.
        assumption.
      + (* Symmetric case *)
        admit.
    - (* Times *)
      admit.
    - (* IfLe *)
      inversion Hsem as [? ? Heval]; subst.
      inversion Heval as [m l Heval']; subst. simpl in Heval'.
      constructor. unfold clean_trace. rewrite last_cons_singleton.
      inversion Heval'; subst.
      + (* Then *)
        admit.
      + (* Else *)
        admit.
    - (* Out: contradiction based on simple well-formedness. *)
      admit.
    - (* Fun *)
      inversion Hsem as [? ? Heval]; subst.
      inversion Heval as [m l Heval']; subst. simpl in Heval'.
      constructor. unfold clean_trace. rewrite last_cons_singleton.
      inversion Heval'; subst.
      + (* Found *)
        change [Result ?X] with (nil ++ [Result X]). constructor. simpl.
        change [] with (@nil event ++ []). econstructor.
        * apply find_clean_ctx in H3. eassumption.
        * (* Standard inductive case (on an existential and other names). *)
          apply eval_main_link_prg in H4.
          pose proof Eval_Prg _ _ _ H4 as Heval1.
          pose proof SemEval _ _ Heval1 as Hsem1.
          assert (Hsem1' : sem (link (Build_par funs_s main) (Build_ctx funs_t)) (targ ++ [Result arg]))
            by admit.
          specialize (IHmain _ _ _ Hsem1' (eq_refl _)).
          unfold clean_trace in IHmain. rewrite last_cons_singleton in IHmain.
          inversion IHmain as [? ? Heval1']; subst.
          inversion Heval1' as [? ? Heval1'' Htrace]; subst.
          unfold link in Heval1''. simpl in Heval1''.
          change [Result ?X] with ([] ++ [Result X]) in Htrace.
          apply app_inj_tail in Htrace as [Ht Hn]; inversion Hn; subst.
          eassumption.
        * eapply eval_fun_clean; last eassumption.
          destruct (core_ctx_wf_clean_expr Hctx_t (wf_ctx_c Hctx_t)) as [Hwf].
          admit. (* By case analysis on the provenance of the function body. *)
      + (* Not found: contradiction based on linkability and well-formedness. *)
        destruct (wf_prg_c (link Hpar_s Hctx_t)) as [_ _ Hcontra].
        inversion Hcontra as [| | | | | ? ? Hcontra' |]; subst.
        unfold link, Hpar_s, Hctx_t in Hcontra'. simpl in Hcontra'.
        apply StringMap.mem_2 in Hcontra'.
        apply StringMapFacts.not_find_in_iff in H0.
        contradiction.
    - (* Arg: contradiction based on simple well-formedness. *)
      destruct (wf_par_c Hpar_s) as [_ Hcontra]. unfold Hpar_s in Hcontra.
      now inversion Hcontra.
  Admitted.


  (* Main theorem. *)
  Theorem extra_target_RTCt : rel_RTC Compiler.chain Source.sem Target.sem trel.
  Proof.
    unfold rel_RTC. simpl. intros par_s ctx_t t Hsem.
    exists (clean_ctx ctx_t), (clean_trace t). split.
    - now apply trel_clean_trace.
    - now apply sem_clean.
  Qed.
End RTCtilde.
