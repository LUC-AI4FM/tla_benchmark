------------------------------ MODULE SquareCheck ------------------------------
EXTENDS Naturals, TLC

(*--algorithm SquareCheckAlg
variables
    x, done;
begin
    (* nondeterministically choose x in 1..10 *)
    x := CHOOSE v \in 1..10 : TRUE;
    ASSERT (x * x <= 100);
    done := TRUE;
end
*)

------------------------------ END MODULE ------------------------------
