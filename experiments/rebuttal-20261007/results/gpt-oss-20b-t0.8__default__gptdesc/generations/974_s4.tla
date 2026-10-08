MODULE RegularRegisterAlg
EXTENDS Naturals, Sequences

CONSTANT N \* positive integer

(* Helper function for neighbor index *)
neighbor(i) == IF i < N THEN i + 1 ELSE 1

\*--algorithm RegularRegisterAlg
variables x = [i \in 1..N |-> {0}],
          y = [i \in 1..N |-> 0],
          pc = [i \in 1..N |-> "start"]

define
    allDone == /\ \A i \in 1..N : pc[i] = "done"
end define

Main(i) ==
    IF pc[i] = "start" THEN
        pc'[i] := "write1";
    ELSIF pc[i] = "write1" THEN
        IF x[i] = {0} THEN
            x'[i] := {0, 1};
            pc'[i] := "write2";
        END IF;
    ELSIF pc[i] = "write2" THEN
        IF x[i] = {0, 1} THEN
            x'[i] := {1};
            pc'[i] := "read";
        END IF;
    ELSIF pc[i] = "read" THEN
        y'[i] := CHOOSE v \in x[neighbor(i)] : v;
        pc'[i] := "done";
    END IF

MainAll == \E i \in 1..N : Main(i)

Next == MainAll
Init == /\ x = [i \in 1..N |-> {0}]
       /\ y = [i \in 1..N |-> 0]
       /\ pc = [i \in 1..N |-> "start"]
Spec == Init /\ [][Next]_ <<x, y, pc>>

Inv == IF allDone THEN (\E i \in 1..N : y[i] = 1) ELSE TRUE
PCorrect == allDone => (\E i \in 1..N : y[i] = 1)

THEOREM InvInvariant == []Inv
THEOREM PCorrectInvariant == []PCorrect

END MODULE