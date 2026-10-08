MODULE RingTermination

EXTENDS Naturals, Sequences, TLC

CONSTANT N = 3
CONSTANT Color == {"red","green"}

VARIABLES tokenAt, tokenColor, act, localColor, terminated

Opposite(c) == IF c="red" THEN "green" ELSE "red"

Init ==
   /\ tokenAt = 0
   /\ tokenColor = "red"
   /\ act = [i \in 0..N-1 |-> FALSE]
   /\ localColor = [i \in 0..N-1 |-> "red"]
   /\ terminated = FALSE

GenerateWork(i) ==
   /\ i \in 0..N-1
   /\ act[i] = FALSE
   /\ act' = [act EXCEPT ![i] = TRUE]
   /\ localColor' = [localColor EXCEPT ![i] = Opposite(localColor[i])]
   /\ UNCHANGED <<tokenAt, tokenColor, terminated>>

ProcessWork(i) ==
   /\ i \in 0..N-1
   /\ act[i] = TRUE
   /\ act' = [act EXCEPT ![i] = FALSE]
   /\ UNCHANGED <<tokenAt, tokenColor, localColor, terminated>>

PassToken ==
   LET i == tokenAt
       next == (i + 1) % N
   IN
      /\ tokenAt' = next
      /\ IF act[i] = FALSE /\ localColor[i] = tokenColor THEN
            tokenColor' = Opposite(tokenColor)
         ELSE
            tokenColor' = tokenColor
      /\ UNCHANGED <<act, localColor, terminated>>

DetectTermination ==
   /\ tokenAt = 0
   /\ tokenColor = "red"
   /\ ∀ i \in 0..N-1 : act[i] = FALSE
   /\ terminated' = TRUE
   /\ UNCHANGED <<tokenAt, tokenColor, act, localColor>>

Next == 
   \/ ∃ i \in 0..N-1 : GenerateWork(i)
   \/ ∃ i \in 0..N-1 : ProcessWork(i)
   \/ PassToken
   \/ DetectTermination

Spec ==
   Init /\ [][Next]_vars /\ WF_vars(PassToken) /\ WF_vars(GenerateWork) /\ WF_vars(ProcessWork) /\ Safety

Safety == 
   /\ tokenAt \in 0..N-1
   /\ tokenColor \in Color
   /\ ∀ i \in 0..N-1 : act[i] \in BOOLEAN
   /\ ∀ i \in 0..N-1 : localColor[i] \in Color

TerminationCorrectness ==
   [] (terminated => ∀ i \in 0..N-1 : act[i] = FALSE)
   /\ [] ((∀ i \in 0..N-1 : act[i] = FALSE) => <> terminated)

Liveness == 
   TerminationCorrectness

END MODULE