---- MODULE TrivialStutter ----
EXTENDS Integers

VARIABLES x

(*--algorithm trivial
variable x = 0;
begin
  while TRUE do
    x := x;
  end while;
end algorithm; *)

Init == x = 0

Next == x' = x

Spec == Init /\ [][Next]_x

============================