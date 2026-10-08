------------------------------ MODULE RingTermination ------------------------------
EXTENDS Naturals

CONSTANTS N
N == 3

CONSTANTS White, Black
White == TRUE
Black == FALSE

VARIABLES active, localColor, tokenPos, tokenColor

vars == <<active, localColor, tokenPos, tokenColor>>

ProcSet == 1..N

NextProc(p) == IF p < N THEN p + 1 ELSE 1

GenerateWork(p) ==
  /\ active[p] = FALSE
  /\ active' = [active EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<localColor, tokenPos, tokenColor>>

CompleteWork(p) ==
  /\ active[p] = TRUE
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ localColor' = [localColor EXCEPT ![p] = NOT localColor[p]]
  /\ UNCHANGED <<tokenPos, tokenColor>>

TokenTransfer(p) ==
  /\ tokenPos = p
  /\ tokenPos' = NextProc(p)
  /\ tokenColor' = IF tokenColor != localColor[p] THEN localColor[p] ELSE tokenColor
  /\ UNCHANGED <<active, localColor>>

Init ==
  /\ active \in [ProcSet -> BOOLEAN]
  /\ localColor \in [ProcSet -> BOOLEAN]
  /\ tokenPos \in ProcSet
  /\ tokenColor \in {White, Black}
  /\ active = [p \in ProcSet |-> FALSE]
  /\ localColor = [p \in ProcSet |-> White]
  /\ tokenPos = 1
  /\ tokenColor = White

Next ==
  \E p \in ProcSet :
    (GenerateWork(p) \/ CompleteWork(p) \/ TokenTransfer(p))

FairGenerateWork == \E p \in ProcSet : GenerateWork(p)
FairCompleteWork == \E p \in ProcSet : CompleteWork(p)
FairTokenTransfer == \E p \in ProcSet : TokenTransfer(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(FairGenerateWork)
  /\ WF_vars(FairCompleteWork)
  /\ WF_vars(FairTokenTransfer)

TokenAtValidProcess == tokenPos \in ProcSet
TokenColorDomain == tokenColor \in {White, Black}
ActiveDomain == \A p \in ProcSet : active[p] \in BOOLEAN
LocalColorDomain == \A p \in ProcSet : localColor[p] \in BOOLEAN

SafetyInvariant == TokenAtValidProcess /\ TokenColorDomain /\ ActiveDomain /\ LocalColorDomain

Quiescent == \A p \in ProcSet : active[p] = FALSE

Terminated == Quiescent /\ tokenColor = White /\ tokenPos = 1

LivenessProperty == [] (Quiescent -> <> Terminated)

------------------------------ END MODULE ------------------------------
