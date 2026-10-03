---- MODULE TrivialInitState ----
EXTENDS Integers

CONSTANTS

VARIABLES x, y

(*
--algorithm trivial_init
begin
  x := 0;
  y := 0;
  while TRUE do
    skip;
  end while;
end algorithm;
*)

Init == 
  /\ x = 0
  /\ y = 0

Next == 
  UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_<<x, y>>

================================