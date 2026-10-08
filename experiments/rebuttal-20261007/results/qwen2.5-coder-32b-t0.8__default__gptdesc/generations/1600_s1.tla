---------------------------- MODULE FastMutualExclusion ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, procState

(* --algorithm fastMutex
variables x = 1,
          y = 1,
          b = [i \in 1..N -> FALSE];

process (p \in 1..N)
begin
retry:
    with j = p do
        b[p] := TRUE;
        while (\E k \in {1 .. N} \ {p}: b[k]) do
            if y < x \/ y = x /\ p < j) then
                b[p] := FALSE;
                await y # x \/ y = x /\ p > j;
                goto retry;
            end if;
        end while;
    end with;

    x := p;
    y := x;

critical:
    skip;

exit:
    b[p] := FALSE;
end process;
end algorithm *)

Init == 
  /\ x = 1
  /\ y = 1
  /\ b \in [1..N -> BOOLEAN]
  /\ (\A i \in 1..N: b[i] = FALSE)
  /\ procState \in [1..N -> {"retry", "critical", "exit"}]

Next ==
  \/ \E p \in 1..N: 
       (procState[p] = "retry" /\
        LET j == p IN
          /\ b' = [b EXCEPT ![p] = TRUE]
          /\ \A k \in {1 .. N} \ {p}: b[k] => y < x \/ y = x /\ p < j
       )
  \/ \E p \in 1..N: 
       (procState[p] = "retry" /\
        LET j == p IN
          /\ b' = [b EXCEPT ![p] = FALSE]
          /\ y # x \/ y = x /\ p > j
          /\ procState' = [procState EXCEPT ![p] = "retry"]
       )
  \/ \E p \in 1..N: 
       (procState[p] = "retry" /\
        LET j == p IN
          /\ b'[p] = TRUE
          /\ (\A k \in {1 .. N} \ {p}: ~b[k])
          /\ x' = p
          /\ y' = p
          /\ procState' = [procState EXCEPT ![p] = "critical"]
       )
  \/ \E p \in 1..N: 
       (procState[p] = "critical" /\
        procState' = [procState EXCEPT ![p] = "exit"]
       )
  \/ \E p \in 1..N: 
       (procState[p] = "exit" /\
        b' = [b EXCEPT ![p] = FALSE]
        /\ procState' = [procState EXCEPT ![p] = "retry"]
       )

Spec == 
  Init /\ [][Next]_<<x, y, b>> /\ WF_next(<<x, y, b>>)

MutualExclusion ==
  \A p1, p2 \in 1..N: 
    \/ ~(procState[p1] = "critical" /\ procState[p2] = "critical")

Liveness ==
  \E p \in 1..N:
    [](<>[](procState[p] = "critical"))

WF_next == WF_vars(<<x, y, b>>)

=============================================================================