Axiom event : Set.
Axiom an_event : event.
Axiom another_event : event.
Axiom different_events : an_event <> another_event.
Axiom eq_event_dec : forall (e1 e2 : event), {e1 = e2} + {e1 <> e2}.
