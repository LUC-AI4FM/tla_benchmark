------------------------------- MODULE ToggleSystem -------------------------------

VARIABLES toggleVar

(*--algorithm ToggleSystem
variables toggleVar = TRUE;

begin
  while TRUE do
    toggleVar := NOT toggleVar;
  end while;
end algorithm;*)

Spec == 
  /\ TYPEOK <<toggleVar>>
  /\ toggleVar \in {TRUE, FALSE}
  /\ [][<<toggleVar>> \in {TRUE, FALSE}]_<<toggleVar>>
  /\ \/ /\ toggleVar = TRUE
     /\ \/ toggleVar' = NOT toggleVar

Prop ==
  /\ [] (toggleVar = TRUE)          \* Intentionally violated property
  /\ [] (toggleVar = toggleVar)      \* Trivially satisfied property
  /\ [] (toggleVar \in {TRUE, FALSE})\* State predicate

=============================================================================