MODULE RingTerminationDetection

CONSTANTS Node

VARIABLES Active, Detected

vars == <<Active, Detected>>

Init ==
  /\ Detected = FALSE
  /\ \A n ∈ Node : Active[n] = TRUE

Terminate ==
  \E n ∈ Node :
    /\ Active[n] = TRUE
    /\ Active' = [Active EXCEPT ![n] = FALSE]
    /\ Detected' = Detected
    /\ Detected = FALSE

Wake ==
  \E n,m ∈ Node : n /= m
    /\ Active[n] = TRUE
    /\ Active[m] = FALSE
    /\ Active' = [Active EXCEPT ![m] = TRUE]
    /\ Detected' = Detected
    /\ Detected = FALSE

Detect ==
  /\ Detected = FALSE
  /\ \A n ∈ Node : Active[n] = FALSE
  /\ Detected' = TRUE
  /\ Active' = Active

Next == Terminate \/ Wake \/ Detect

Spec ==
  Init /\ [][Next]_vars /\ WF(Detect)

Correctness ==
  [] (Detected => \A n ∈ Node : Active[n] = FALSE)

Quiescence ==
  [] (Detected => \A n ∈ Node : Active[n] = FALSE)

Liveness ==
  []( (\A n ∈ Node : Active[n] = FALSE) => <> Detected )