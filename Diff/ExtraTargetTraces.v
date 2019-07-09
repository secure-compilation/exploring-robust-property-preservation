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

  (* Programs and contexts with their well-formedness conditions. *)
  Record par_wf (funs : funmap) (main : expr) :=
    {
      par_wf_funless : funmap_funless funs;
      par_wf_argless : argless main
    }.

  Record par :=
    {
      par_funs : funmap;
      par_main : expr;
      par_prop : par_wf par_funs par_main
    }.

  Record ctx_wf (funs : funmap) :=
    {
      ctx_wf_funless : funmap_funless funs
    }.

  Record ctx :=
    {
      ctx_funs : funmap;
      ctx_prop : ctx_wf ctx_funs
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
      prg_prop : prg_wf prg_funs prg_main
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
      wf_empty_prg.

  (* Second, compose proper well-formedness proofs. *)
  Definition link_fun (par_fun ctx_fun : option expr) :=
    match par_fun, ctx_fun with
    | Some f, _ => Some (ProgramTurn, f)
    | _, Some f => Some (ContextTurn, f)
    | _, _ => None
    end.

  Definition link_funs (p : par) (c : ctx) :=
    StringMap.map2 link_fun (par_funs p) (ctx_funs c).

  Lemma link_wf  (p : par) (c : ctx) :
    closed (link_funs p c) (par_main p) = true ->
    par_wf (par_funs p) (par_main p) ->
    ctx_wf (ctx_funs c) ->
    prg_wf (link_funs p c) (par_main p).
  Admitted.

  (* RB: Check how this works inside proofs. *)
  Definition link (p : par) (c : ctx) : prg.
    set (prg_funs := link_funs p c).
    destruct (closed prg_funs (par_main p)) eqn:Hisclosed.
    - exact (Build_prg
               prg_funs
               (par_main p)
               (link_wf _ _ Hisclosed (par_prop p) (ctx_prop c))).
    - (* Bad case, can be ruled out by well-formedness but to clean up. *)
      exact empty_prg.
  Defined.

  (* Traces as evaluation results. *)
  Inductive trace :=
  | Result : nat -> trace
  | Output : nat -> trace -> trace.

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
      par_prop : par_wf par_core
    }.

  Record ctx_wf (c : Core.ctx) :=
    {
      ctx_wf_funs_outless : funmap_outless (Core.ctx_funs c);
    }.

  Record ctx :=
    {
      ctx_core : Core.ctx;
      ctx_prop : ctx_wf ctx_core
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
      prg_prop : prg_wf prg_core
    }.

  (* Wrap link operation and define language. *)
  Lemma link_wf (p : par) (c : ctx) :
    par_wf (par_core p) ->
    ctx_wf (ctx_core c) ->
    prg_wf (Core.link (par_core p) (ctx_core c)).
  Admitted.

  Definition link (p : par) (c : ctx) : prg :=
    Build_prg
      (Core.link (par_core p) (ctx_core c))
      (link_wf _ _ (par_prop p) (ctx_prop c)).

  Definition lang := Build_Language link.

  (* Wrap core and define semantics. *)
  Definition sem_wrap (p : prg) : Core.trace -> Prop := Core.sem (prg_core p).

  Remark trace_exists : forall W : prg, exists t : Core.trace, sem_wrap W t.
    intros [Wcore Wout]. exists (Core.eval_prg Wcore). now apply Core.SemEval.
  Qed.

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
  (* A simple trace relation that does not track program-context changes. It
     will say less about the target in the source, but also be a bit easier to
     prove. *)
  Inductive trel : Core.trace -> Core.trace -> Prop :=
  | RelResult : forall ns nt,
      trel (Core.Result ns) (Core.Result nt)
  | RelOutput : forall ns nt t,
      trel (Core.Result ns) t -> trel (Core.Result ns) (Core.Output nt t).

  (* Clean up contexts and traces.
       RB: Better names to avoid Core vs. Target and Source confusion. *)
  Fixpoint clean_expr (e : Core.expr) : Core.expr :=
    match e with
    | Core.Const _ | Core.Arg => e
    | Core.Plus e1 e2 => Core.Plus (clean_expr e1) (clean_expr e2)
    | Core.Times e1 e2 => Core.Times (clean_expr e1) (clean_expr e2)
    | Core.Out _ e' => clean_expr e'
    | Core.IfLe econd1 econd2 ethen eelse =>
      Core.IfLe (clean_expr econd1) (clean_expr econd2)
                (clean_expr ethen) (clean_expr eelse)
    | Core.Fun f e' => Core.Fun f (clean_expr e')
    end.

  Lemma core_ctx_wf_clean_expr (ctx : Core.ctx) :
    Core.ctx_wf (Core.ctx_funs ctx) ->
    Core.ctx_wf (StringMap.map clean_expr (Core.ctx_funs ctx)).
  Admitted.

  Definition clean_ctx_core (ctx : Core.ctx) :=
    (Core.Build_ctx
       (StringMap.map clean_expr (Core.ctx_funs ctx))
       (core_ctx_wf_clean_expr _ (Core.ctx_prop ctx))).

  Lemma source_ctx_wf_clean_expr (ctx : Core.ctx) :
    Source.ctx_wf (clean_ctx_core ctx).
  Admitted.

  Definition clean_ctx (ctx : Core.ctx) : Source.ctx :=
    Source.Build_ctx
      (clean_ctx_core ctx)
      (source_ctx_wf_clean_expr _).

  Fixpoint clean_trace (t : Core.trace) : Core.trace :=
    match t with
    | Core.Result n => t
    | Core.Output n t' => clean_trace t'
    end.

  (* Properties of trace cleanup. *)
  Lemma clean_trace_result : forall t, exists n, clean_trace t = Core.Result n.
  Proof.
    intros t. induction t as [n | n t [n' IHt]].
    - now exists n.
    - now exists n'.
  Qed.

  Lemma trel_clean_trace : forall t, trel (clean_trace t) t.
  Proof.
    intros t. induction t as [| n t IHt].
    - now constructor.
    - simpl. destruct (clean_trace_result t) as [n' Hclean].
      rewrite Hclean in *. now constructor.
  Qed.

  (* Properties of context cleanup. *)

  (* Main theorem. *)
  Theorem extra_target_RTCt : rel_RTC Compiler.chain Source.sem Target.sem trel.
  Proof.
    unfold rel_RTC. simpl. intros [par_s Houtless] ctx_t t Hsem.
    exists (clean_ctx ctx_t), (clean_trace t). simpl in Hsem. split.
    - now apply trel_clean_trace.
    - unfold Source.sem_wrap.
      unfold Compiler.comp_par in Hsem. simpl.
  Admitted.
End RTCtilde.
