---- MODULE SimpleCounter ----
EXTENDS Naturals

VARIABLES x

(*
--algorithm simple_counter
begin
  x := 0;
  while x < 3 do
    x := x + 1;
  end while;
  while TRUE do
    x := x;
  end while;
end algorithm;
*)

Init == x = 0

Increment == x < 3 /\ x' = x + 1

StutterAtMax == x >= 3 /\ x' = x

Next == Increment \/ StutterAtMax

Spec == Init /\ [][Next]_x

============================