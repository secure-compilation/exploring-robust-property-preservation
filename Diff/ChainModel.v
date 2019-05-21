Require Import TraceModel.
Require Import Properties.
Require Import LanguageModel.
Require Import Galois. 
Require Import MyNotation.

Module Type RelTrace (TSource TTarget : Trace).
  
  Parameter rel: TSource.trace -> TTarget.trace -> Prop.

  Module SProp := Properties TSource.
  Module TProp := Properties TTarget. 
  
  Definition prop__S := SProp.prop.
  Definition prop__T := TProp.prop. 

  Definition adjunction :=  induced_connection rel.  
  
  Definition τ' : prop__S -> prop__T := α adjunction.   
  Definition σ' : prop__T -> prop__S := γ adjunction.  

  Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction. 
      
End RelTrace.

Module Type CompilationChain (Source Target : Language). 
  
  Parameter compile_whole : Source.prg -> Target.prg.
  Parameter compile_par   : Source.par -> Target.par.
  Parameter compile_ctx   : Source.ctx -> Target.ctx.
  
End CompilationChain. 

Module Type TCtilde_Chain (TSource TTarget : Trace)
                          (R : RelTrace TSource TTarget)
                          (Source Target : Language)  <:
                          (CompilationChain Source Target).

  Module Sat__S := Sat TSource Source.
  Module Sat__T := Sat TTarget Target.

  Definition sem__S := Sat__S.sem.
  Definition sem__T := Sat__T.sem.

  (*CA: probably there is a way to not to write again these compile_* *)
  Parameter compile_whole : Source.prg -> Target.prg.
  Parameter compile_par   : Source.par -> Target.par.
  Parameter compile_ctx   : Source.ctx -> Target.ctx.

  Notation "W ↓" := (compile_whole W) (at level 50).
                   
  Parameter correctness : forall W__S t__T, sem__T (W__S ↓) t__T -> exists t__S, R.rel t__S t__T.
  
End TCtilde_Chain.