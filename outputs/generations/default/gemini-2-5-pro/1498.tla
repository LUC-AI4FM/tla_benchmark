---- MODULE SimpleStateMachine ----
EXTENDS TLC, Booleans

VARIABLES x

TypeOk == x \in BOOLEAN

(*
--algorithm simple_state_machine
variables x = FALSE;
begin
  while TRUE do
    either
      A:
        x := ~x;
    or
      B:
        x := ~x;
    end either;
  end while;
end algorithm;
*)

Switch(v) == ~v

Init == x = FALSE

A == x' = Switch(x)

B == x' = Switch(x)

Next == A \/ B

Spec == Init /\ [][Next]_x

=============================================================================