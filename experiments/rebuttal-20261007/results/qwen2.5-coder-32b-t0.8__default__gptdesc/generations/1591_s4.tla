---- MODULE EvenOdd ----
EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

Init == 
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = << >>
  /\ xOdd = << >>
  /\ result = FALSE

Next ==
  \/ /\ pc = "Start"
     /\ (N = 0) -> pc' = "Done" /\ result' = TRUE
     /\ (N # 0) -> pc' = "CheckParity" 
  \/ /\ pc = "CheckParity"
     /\ (N % 2 = 0) -> pc' = "Even" /\ stack' = << "Odd", N >> @@ stack
     /\ (N % 2 # 0) -> pc' = "Odd" /\ stack' = << "Even", N >> @@ stack
  \/ /\ pc = "Even"
     /\ xEven = << >> -> result' = TRUE /\ pc' = "Done"
     /\ xEven # << >> -> LET n == HD(xEven)
                        IN  /\ pc' = "CheckParity" 
                            /\ stack' = TL(stack)
                            /\ xEven' = TL(xEven) 
                            /\ N' = n
  \/ /\ pc = "Odd"
     /\ xOdd = << >> -> result' = FALSE /\ pc' = "Done"
     /\ xOdd # << >> -> LET n == HD(xOdd)
                        IN  /\ pc' = "CheckParity" 
                            /\ stack' = TL(stack)
                            /\ xOdd' = TL(xOdd) 
                            /\ N' = n
  \/ /\ pc = "Done"

Spec ==
  Init /\ [][Next]_<<pc, stack, xEven, xOdd, result>> /\ WF_next(<<pc, stack, xEven, xOdd, result>>, Next)

\* Safety invariants
TerminationInvariant == (pc = "Done" => \A s \in SUBSET stack: #s % 2 = 0)
Correctness ==
  \/ pc # "Done"
  \/ /\ pc = "Done"
     /\ IF N % 2 = 0 THEN result ELSE ~result

\* Liveness property
TerminationProperty == <>[](pc = "Done")

====