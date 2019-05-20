Require Import TraceModel.
Require Import LanguageModel.

Module Type RelTrace (TSource TTarget : Trace).
  
  Parameter rel : TSource.trace -> TTarget.trace -> Prop.
  
End RelTrace.

Module Type CompilationChain (TSource TTarget : Trace) (R : RelTrace TSource TTarget)
       (Source : Language TSource) (Target : Language TTarget).
  Import R.

  Parameter compile_whole : Source.prg -> Target.prg.
  Parameter compile_par : Source.par -> Target.par.

End CompilationChain.

Module Type CorrectCompilationChain (TSource TTarget : Trace) (R : RelTrace TSource TTarget)
       (Source : Language TSource) (Target : Language TTarget) <:
  (CompilationChain TSource TTarget R Source Target).

  Import R.

  Parameter compile_whole : Source.prg -> Target.prg.
  Parameter compile_par : Source.par -> Target.par.
  Parameter correctness : forall Ws tt, Target.sem (compile_whole Ws) tt -> exists ts, rel ts tt.
  
End CorrectCompilationChain.