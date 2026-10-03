---- MODULE SimpleBoolean ----
EXTENDS TLC

VARIABLES x

(*--algorithm simple
variable x = TRUE;
begin
  A:
    while TRUE do
      x := ~x;
    end while;
end algorithm; *)

TypeOK == x \in BOOLEAN

IsTrue  == x = TRUE
IsFalse == x = FALSE

Init == x = TRUE

Next == x' = ~x

Spec == Init /\ [][Next]_x

====