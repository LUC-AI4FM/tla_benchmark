---- MODULE MaxFinder ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Inputs, MinValue

ASSUME /\ \A s \in Inputs : s \in Seq(Int)
       /\ MinValue \in Int
       /\ \A s \in Inputs : \A i \in 1..Len(s) : MinValue < s[i]

VARIABLES inp, result, remaining, pc

vars == <<inp, result, remaining, pc>>

TypeOK ==
    /\ inp \in Inputs
    /\ result \in Int
    /\ remaining \subseteq 1..Len(inp)
    /\ pc \in {"Lbl_1", "Done"}

Init ==
    /\ inp \in Inputs
    /\ result = MinValue
    /\ remaining = 1..Len(inp)
    /\ pc = "Lbl_1"

Step ==
    /\ pc = "Lbl_1"
    /\ remaining # {}
    /\ \E i \in remaining :
         /\ result' = IF inp[i] > result THEN inp[i] ELSE result
         /\ remaining' = remaining \ {i}
    /\ UNCHANGED <<inp, pc>>

Finish ==
    /\ pc = "Lbl_1"
    /\ remaining = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<inp, result, remaining>>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

\* Safety: invariant maintained during processing
Processed == (1..Len(inp)) \ remaining

LoopInvariant ==
    /\ (Processed = {}) => (result = MinValue)
    /\ (Processed # {}) =>
         /\ \E i \in Processed : result = inp[i]
         /\ \A i \in Processed : result >= inp[i]

\* Safety: correctness upon termination
Correctness ==
    pc = "Done" =>
        /\ (inp = <<>>) => (result = MinValue)
        /\ (inp # <<>>) =>
             /\ \E i \in 1..Len(inp) : result = inp[i]
             /\ \A i \in 1..Len(inp) : result >= inp[i]

\* Liveness: the algorithm always terminates
Termination == <>(pc = "Done")

\* Liveness: progress - remaining work eventually drains
Progress == \A n \in Nat : (Cardinality(remaining) = n /\ n > 0) ~> (Cardinality(remaining) < n)

====