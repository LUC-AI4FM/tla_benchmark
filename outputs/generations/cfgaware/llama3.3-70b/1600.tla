--------------------------- MODULE FastMutualExclusion ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, b, j, failed

defaultInitValue == <<0, 0, [i \in 1..N |-> FALSE], [i \in 1..N |-> 0], [i \in 1..N |-> FALSE]>>

TypeInvariant == x \in (1..N) /\ y \in (1..N) /\ b \in [1..N -> BOOLEAN] 
                  /\ j \in [1..N -> 0..2] /\ failed \in [1..N -> BOOLEAN]

Init == (* Initial state *)
       /\ x = 0
       /\ y = 0
       /\ b = [i \in 1..N |-> FALSE]
       /\ j = [i \in 1..N |-> 0]
       /\ failed = [i \in 1..N |-> FALSE]

Next(i \in 1..N) == 
  IF j[i] = 0 THEN
    (* Try to enter critical section *)
    OR
      b[i] := TRUE;
      IF y = i THEN
        x := i;
        y := 0;
        j[i] := 2
      ELSE
        failed[i] := TRUE;
        j[i] := 1
  ELSE IF j[i] = 1 THEN
    (* Retry after failure *)
    b[i] := FALSE;
    failed[i] := FALSE;
    j[i] := 0
  ELSE 
    (* Exit critical section *)
    b[i] := FALSE;
    j[i] := 0

Next == \E i \in 1..N : Next(i)

Invariant == \A i, j \in 1..N : i # j => ~(x = i /\ x = j)
Liveness == <>[](\E i \in 1..N : j[i] = 2)

Spec == Init /\ [][Next]_<<x, y, b, j, failed>> 
         /\ WF_i(i \in 1..N)(Next(i))

THEOREM Spec => []Invariant
THEOREM Spec => Liveness

=============================================================================