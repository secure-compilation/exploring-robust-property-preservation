Require Import TraceModel.
Require Import Properties.
Require Import LanguageModel.
Require Import Galois. 
Require Import MyNotation.


Record CompilationChain (Source Target : Language) := { 
  
   compile_whole : prg Source -> prg Target;
   compile_par   : par Source -> par Target;
   compile_ctx   : ctx Source -> ctx Target

  }. 


(* Section RelTrace. *)

(*   Variable Σ__S Σ__T States__S States__T : Set. *)
(*   Variable E__S : Events Σ__S. *)
(*   Variable E__T : Events Σ__T. *)
(*   Variable S__S : EndState States__S. *)
(*   Variable S__T : EndState States__T. *)

(*   Local Definition trace__S := trace Σ__S States__S.  *)
(*   Local Definition trace__T := trace Σ__T States__T.   *)
  
(*   Parameter rel: trace__S -> trace__T -> Prop. *)

(*   Local Definition prop__S := prop Σ__S States__S. *)
(*   Local Definition prop__T := prop Σ__T States__T. *)
  
(*   Definition adjunction :=  induced_connection rel.   *)
  
(*   Definition τ' : prop__S -> prop__T := α adjunction.    *)
(*   Definition σ' : prop__T -> prop__S := γ adjunction.   *)

(*   Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.  *)

(* End RelTrace. *)

