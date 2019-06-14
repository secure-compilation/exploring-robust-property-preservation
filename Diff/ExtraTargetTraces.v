Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapWeakList.
Require Import TraceModel.
Require Import LanguageModel.

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

(* Base expressions. *)
Inductive expr : Set :=
| Const : nat -> expr
| Plus  : expr -> expr -> expr
| Times : expr -> expr -> expr
| IfLe  : expr -> expr -> expr -> expr -> expr.

(* Source language. *)
Module Src.

  (* Simple expressions and function types.
     RB: At the moment, functions cannot call other functions! *)
  Definition expr_fun : Set := expr.
  Definition funType : Set := expr_fun -> expr_fun.

  (* Program expressions. *)
  Inductive expr_par : Set :=
  | Expr : expr -> expr_par
  | Fun  : string -> expr_par -> expr_par.

  (* Programs and contexts (as records, Type and not Set). *)
  Record par :=
    {
      par_funs : StringMap.t funType;
      par_main : expr_par
    }.

  Record ctx :=
    {
      ctx_funs : StringMap.t funType
    }.

  Record prg := (* Type, not Set. *)
    {
      prg_funs : StringMap.t (turn * funType);
      prg_main : expr_par
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
      (par_main p).

  Fail Build_Language link.

  (* Traces as evaluation results. *)
  Inductive trace :=
  | Result : nat -> trace.

  (* Evaluation-based semantics. *)
  Definition eval (p : prg) : nat := 0. (* TODO *)

  Inductive sem : prg -> trace -> Prop :=
  | SemEval : forall p n, eval p = n -> sem p (Result n).
End Src.
