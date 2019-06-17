Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapWeakList.
Require Import TraceModel.
Require Import LanguageModel.
Require Import ChainModel.

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

Module StringMap : WS := Make DecidableString.

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
  Inductive expr : Set :=
  | Const : nat -> expr
  | Plus  : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | IfLe  : expr -> expr -> expr -> expr -> expr
  | Out   : expr -> expr -> expr
  | Fun   : string -> expr -> expr.

  (* Function types.
       RB: At the moment, functions should not call other functions! *)
  Definition funType : Set := expr -> expr.

  (* Programs and contexts (as records, Type and not Set). *)
  Record par :=
    {
      par_funs : StringMap.t funType;
      par_main : expr;
      par_wf   : False (* TODO: Add well-formedness conditions. *)
    }.

  Record ctx :=
    {
      ctx_funs : StringMap.t funType;
      ctx_wf   : False (* TODO: Add well-formedness conditions. *)
    }.

  Record prg := (* Type, not Set. *)
    {
      prg_funs : StringMap.t (turn * funType);
      prg_main : expr;
      prg_wf   : False (* TODO: Add well-formedness conditions. *)
    }.

  (* Linking. Assume main in the program and combine functions from program and
     context with tags to remember provenance.
     RB: Clashes are resolved by favoring the program side, but should never
     be allowed. *)
  Definition link_fun (par_fun ctx_fun : option funType) :=
    match par_fun, ctx_fun with
    | Some f, _ => Some (ProgramTurn, f)
    | _, Some f => Some (ContextTurn, f)
    | _, _ => None
    end.

  Definition link (p : par) (c : ctx) : prg :=
    Build_prg
      (StringMap.map2 link_fun (par_funs p) (ctx_funs c))
      (par_main p)
      (par_wf p). (* TODO *)

  (* Traces as evaluation results. *)
  Inductive trace :=
  | Output : nat -> trace -> trace
  | Result : nat -> trace.

  (* Evaluation-based semantics, returns both trace and result.
       RB: An Out expression can itself produce traces, which is nonstandard.
     Should it? *)
  Definition eval_prg (p : prg) : trace :=
    let fix eval (e : expr) : (nat * list nat) :=
        match e with
        | Const n => (n, [])
        | Plus e1 e2 =>
          match eval e1, eval e2 with
          | (n1, t1), (n2, t2) => (n1 + n2, t1 ++ t2)
          end
        | Times e1 e2 =>
          match eval e1, eval e2 with
          | (n1, t1), (n2, t2) => (n1 * n2, t1 ++ t2)
          end
        | IfLe ecomp1 ecomp2 ethen eelse =>
          match eval ecomp1, eval ecomp2 with
          | (n1, t1), (n2, t2) =>
            if n1 <=? n2
            then let '(n, t) := eval ethen in (n, t1 ++ t2 ++ t)
            else let '(n, t) := eval eelse in (n, t1 ++ t2 ++ t)
          end
        | Out eout e =>
          match eval eout, eval e with
          | (nout, tout), (n, t) => (n, tout ++ [nout] ++ t)
          end
        | Fun id arg => (0, []) (* TODO *)
        end
    in
    let fix gen_trace (res: nat) (outs : list nat) : trace :=
        match outs with
        | [] => Result res
        | out :: outs' => Output out (gen_trace res outs')
        end
    in
    let '(n, t) := eval (prg_main p) in gen_trace n t.

  Inductive sem : prg -> trace -> Prop :=
  | SemEval : forall p t, eval_prg p = t -> sem p t.

  Remark trace_exists : forall W : prg, exists t : trace, sem W t.
    intro W. exists (eval_prg W). now apply SemEval.
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

  Inductive outless_prg : Core.prg -> Prop :=
  | OutlessPrg : forall prg,
      outless_expr (Core.prg_main prg) -> outless_prg prg.
  (* TODO: Deal with functions. *)

  (* Decorate core programs with their additional property. *)
  Record par :=
    {
      par_core    : Core.par;
      par_outless : False (* TODO: Add well-formedness conditions. *)
    }.

  Record ctx :=
    {
      ctx_core    : Core.ctx;
      ctx_outless : False (* TODO: Add well-formedness conditions. *)
    }.

  Record prg :=
    {
      prg_core    : Core.prg;
      prg_outless : False (* TODO: Add well-formedness conditions. *)
    }.

  (* Wrap link operation and define language. *)
  Definition link (p : par) (c : ctx) : prg :=
    Build_prg
      (Core.link (par_core p) (ctx_core c))
      (par_outless p). (* TODO *)

  Definition lang := Build_Language link.

  (* Wrap core and define semantics. *)
  Definition sem_wrap (p : prg) : Core.trace -> Prop := Core.sem (prg_core p).

  Remark trace_exists : forall W : prg, exists t : Core.trace, sem_wrap W t.
    intros [Wcore Wout]. exists (Core.eval_prg Wcore). now apply Core.SemEval.
  Qed.

  Definition sem := Build_Semantics lang sem_wrap trace_exists.
End Source.

(* Compiler. *)
Section Compiler.
  (* Build the identity compiler from the shared core and define the chain.
       Observe that this transformation amounts to stripping off the extra,
     source-only properties stating the absence of Out commands and their
     associated events. *)
  Definition comp_prg (p : prg Source.lang) : prg Target.lang := Source.prg_core p.
  Definition comp_par (p : par Source.lang) : par Target.lang := Source.par_core p.
  Definition comp_ctx (c : ctx Source.lang) : ctx Target.lang := Source.ctx_core c.

  Definition chain :=
    Build_CompilationChain Source.lang Target.lang comp_prg comp_par comp_ctx.
Section Compiler.