Variant level :=
  source : level
| target : level.

Axiom event : level -> Set.  
Axiom an_event another_event : forall l, event l.
Axiom different_events : forall l, an_event l <> another_event l.
Axiom eq_event_dec : forall {l} (e1 e2 : event l), {e1 = e2} + {e1 <> e2}. 

Axiom endstate : level -> Set.
Axiom an_endstate : forall {l}, endstate l.

Axiom is_input : forall {l}, event l -> Prop.
