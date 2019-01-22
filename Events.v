(** This file defines an abstract model of the events
    that will be used in the traces 

    In particular, we assume that there exists at least
    two different events.
*)

Axiom event : Set.
Axiom an_event : event.
Axiom another_event : event.
Axiom different_events : an_event <> another_event.
Axiom eq_event_dec : forall (e1 e2 : event), {e1 = e2} + {e1 <> e2}. 

Axiom endstate : Set.
Axiom an_endstate : endstate.

Axiom is_input : event -> Prop.
