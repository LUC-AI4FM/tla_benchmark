------------------------------- MODULE CircleAlgorithm -------------------------------

CONSTANTS N

VARIABLES array1, array2, pc

(*--algorithm CircleAlgorithm
variables array1 = [i \in 0..N-1 |-> 0],
          array2 = [i \in 0..N-1 |-> 0],
          pc     = [i \in 0..N-1 |-> "start"]

process (p \in 0..N-1)
begin
Step1:
    if pc[p] = "start" then
        array1[p] := 1;
        pc[p] := "step2";
    end if;

Step2:
    if pc[p] = "step2" then
        let leftNeighbor == (p - 1) % N in
            array2[p] := array1[leftNeighbor];
            pc[p] := "done";
    end if;
end process; *)
\* END ALGORITHM

Spec ==
    /\ \E array1, array2, pc \in [0..N-1 -> Nat] : Init
    /\ [][Next]_<<pc>>
    /\ WF_next(<<pc>>)

Init ==
    /\ array1 = [i \in 0..N-1 |-> 0]
    /\ array2 = [i \in 0..N-1 |-> 0]
    /\ pc     = [i \in 0..N-1 |-> "start"]

Next ==
    \/ \E p \in 0..N-1 : Step1(p)
    \/ \E p \in 0..N-1 : Step2(p)

Step1(p) ==
    /\ pc[p] = "start"
    /\ array1' = [array1 EXCEPT ![p] = 1]
    /\ array2' = array2
    /\ pc'     = [pc EXCEPT ![p] = "step2"]

Step2(p) ==
    /\ pc[p] = "step2"
    /\ LET leftNeighbor == (p - 1) % N IN
        /\ array1' = array1
        /\ array2' = [array2 EXCEPT ![p] = array1[leftNeighbor]]
        /\ pc'     = [pc EXCEPT ![p] = "done"]

WF_next(vars) ==
    WF_vars(Next, vars)

PCorrect ==
    Spec /\ []<>(\A p \in 0..N-1 : pc[p] = "done") => <>(\E i \in 0..N-1 : array2[i] = 1)

TypeOK ==
    /\ array1 \in [0..N-1 -> {0, 1}]
    /\ array2 \in [0..N-1 -> {0, 1}]
    /\ pc     \in [0..N-1 -> {"start", "step2", "done"}]

Inv ==
    /\ TypeOK
    /\ (\A p \in 0..N-1 : pc[p] = "done" => array2[p] = array1[(p - 1) % N])

=============================================================================