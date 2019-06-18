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

  (* Well-formedness conditions. *)
  (* TODO *)

  (* Programs and contexts (as records, Type and not Set). *)
  Record par :=
    {
      par_funs : funmap;
      par_main : expr;
      par_wf   : False (* TODO: Add well-formedness conditions. *)
                 (* funmap_funless par_funs /\ *)
                 (* argless par_main *)
    }.

  Record ctx :=
    {
      ctx_funs : funmap;
      ctx_wf   : False (* TODO: Add well-formedness conditions. *)
                 (* funmap_funless ctx_funs *)
    }.

  Record prg := (* Type, not Set. *)
    {
      prg_funs : funmap_turn;
      prg_main : expr;
      prg_wf   : False (* TODO: Add well-formedness conditions. *)
                 (* funmap_funless (funmap_turn_bodies prg_funs) /\ *)
                 (* argless prg_main /\ *)
                 (* well_formed_calls prg_funs prg_main *)
    }.

  (* Linking. Assume main in the program and combine functions from program and
     context with tags to remember provenance.
     RB: Clashes are resolved by favoring the program side, but should never
     be allowed. *)
  Definition link_fun (par_fun ctx_fun : option expr) :=
    match par_fun, ctx_fun with
    | Some f, _ => Some (ProgramTurn, f)
    | _, Some f => Some (ContextTurn, f)
    | _, _ => None
    end.

  Definition link (p : par) (c : ctx) : prg :=
    let prg_funs := (StringMap.map2 link_fun (par_funs p) (ctx_funs c)) in
    if closed prg_funs (par_main p) then
      Build_prg
        prg_funs
        (par_main p)
        (par_wf p) (* TODO *)
    else (* Bad case, can be ruled out by well-formedness but to clean up. *)
      Build_prg
        (StringMap.empty _)
        (Const 0)
        (par_wf p). (* TODO *)

  (* Traces as evaluation results. *)
  Inductive trace :=
  | Output : nat -> trace -> trace
  | Result : nat -> trace.

  (* Evaluation-based semantics, returns both trace and result.
       RB: An Out expression can itself produce traces, which is nonstandard.
     Should it?
       RB: Rename to eval?
       RB: Currently no program-context switching information recorded.
       RB: Also currently, getting away with two simple but mostly redundant
     fixpoints. *)
  Definition eval_fun (arg : nat) (e : expr) : (nat * list nat) :=
    let fix eval e :=
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
        | Out eout e' =>
          match eval eout, eval e' with
          | (nout, tout), (n, t) => (n, tout ++ [nout] ++ t)
          end
        | Fun id earg => (0, []) (* Bad case, rule out in closed programs. *)
        | Arg => (arg, [])
        end
    in eval e.

  Definition eval_main (fs : funmap_turn) (e : expr) : (nat * list nat) :=
    let fix eval e :=
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
        | Out eout e' =>
          match eval eout, eval e' with
          | (nout, tout), (n, t) => (n, tout ++ [nout] ++ t)
          end
        | Fun id earg =>
          let '(arg, targ) := eval earg in
          match StringMap.find id fs with
          | Some (_, e') =>
            let '(n, t) := eval_fun arg e' in
            (n, targ ++ t)
          | None => (0, []) (* Bad case, rule out in closed programs. *)
          end
        | Arg => (0, []) (* Bad case, ruled out by main. *)
        end
    in eval e.

  Definition eval_prg (p : prg) : trace :=
    let fix gen_trace (res: nat) (outs : list nat) : trace :=
        match outs with
        | [] => Result res
        | out :: outs' => Output out (gen_trace res outs')
        end
    in let '(n, t) := eval_main (prg_funs p) (prg_main p) in gen_trace n t.

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
End Compiler.
