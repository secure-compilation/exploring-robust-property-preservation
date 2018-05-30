Record Components :=
  {
    prg  : Set;
    ctx  : Set; 
    plug : prg -> ctx -> prg          
  }.

Axiom source : Components.
Axiom target : Components.
Axiom compile : (prg source) -> (prg target).






