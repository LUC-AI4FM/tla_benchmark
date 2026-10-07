----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME M \in Nat /\ N \in Nat /\ 1 <= M /\ M < N

(*
  Two process classes:
    ProcL = 1..M
    ProcR = (M+1)..N
  Shared variables: x, y, b
*)

Null == 0
Proc  == 1..N
ProcL == 1..M
ProcR == (M+1)..N

LLabels == {"l1","l2","l3","l4a","l5","l6","l8","l9","lcs","lexit1","lexit2"}
RLabels == {"r1","r2","r3","r4a","r5","r6","r8","r9","rcs","rexit1","rexit2"}

VARIABLES x, y, b, pc

TypeOK ==
  /\ x \in Proc \cup {Null}
  /\ y \in Proc \cup {Null}
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> (LLabels \cup RLabels)]

Init ==
  /\ x = Null
  /\ y = Null
  /\ b = [p \in Proc |-> FALSE]
  /\ pc = [p \in Proc |-> IF p \in ProcL THEN "l1" ELSE "r1"]

InCS(p) == (p \in ProcL /\ pc[p] = "lcs") \/ (p \in ProcR /\ pc[p] = "rcs")

MutualExclusion ==
  \A p \in Proc: \A q \in Proc:
    p # q => ~(InCS(p) /\ InCS(q))

StepL(i) ==
  /\ i \in ProcL
  /\ (
      /\ pc[i] = "l1"
      /\ b'  = [b EXCEPT ![i] = TRUE]
      /\ UNCHANGED <<x, y>>
      /\ pc' = [pc EXCEPT ![i] = "l2"]
     \/
      /\ pc[i] = "l2"
      /\ x'  = i
      /\ UNCHANGED <<y, b>>
      /\ pc' = [pc EXCEPT ![i] = "l3"]
     \/
      /\ pc[i] = "l3" /\ y # Null
      /\ b'  = [b EXCEPT ![i] = FALSE]
      /\ UNCHANGED <<x, y>>
      /\ pc' = [pc EXCEPT ![i] = "l4a"]
     \/
      /\ pc[i] = "l3" /\ y = Null
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![i] = "l5"]
     \/
      /\ pc[i] = "l4a" /\ y = Null
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![i] = "l1"]
     \/
      /\ pc[i] = "l5"
      /\ y'  = i
      /\ UNCHANGED <<x, b>>
      /\ pc' = [pc EXCEPT ![i] = "l6"]
     \/
      /\ pc[i] = "l6" /\ x # i
      /\ b'  = [b EXCEPT ![i] = FALSE]
      /\ UNCHANGED <<x, y>>
      /\ pc' = [pc EXCEPT ![i] = "l8"]
     \/
      /\ pc[i] = "l6" /\ x = i
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![i] = "lcs"]
     \/
      /\ pc[i] = "l8"
      /\ \A j \in Proc: j = i \/ b[j] = FALSE
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![i] = "l9"]
     \/
      /\ pc[i] = "l9" /\ y # i /\ y = Null
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![i] = "l1"]
     \/
      /\ pc[i] = "l9" /\ y = i
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![i] = "lcs"]
     \/
      /\ pc[i] = "lcs"
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![i] = "lexit1"]
     \/
      /\ pc[i] = "lexit1"
      /\ y'  = Null
      /\ UNCHANGED <<x, b>>
      /\ pc' = [pc EXCEPT ![i] = "lexit2"]
     \/
      /\ pc[i] = "lexit2"
      /\ b'  = [b EXCEPT ![i] = FALSE]
      /\ UNCHANGED <<x, y>>
      /\ pc' = [pc EXCEPT ![i] = "l1"]
     )

StepR(j) ==
  /\ j \in ProcR
  /\ (
      /\ pc[j] = "r1"
      /\ b'  = [b EXCEPT ![j] = TRUE]
      /\ UNCHANGED <<x, y>>
      /\ pc' = [pc EXCEPT ![j] = "r2"]
     \/
      /\ pc[j] = "r2"
      /\ x'  = j
      /\ UNCHANGED <<y, b>>
      /\ pc' = [pc EXCEPT ![j] = "r3"]
     \/
      /\ pc[j] = "r3" /\ y # Null
      /\ b'  = [b EXCEPT ![j] = FALSE]
      /\ UNCHANGED <<x, y>>
      /\ pc' = [pc EXCEPT ![j] = "r4a"]
     \/
      /\ pc[j] = "r3" /\ y = Null
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![j] = "r5"]
     \/
      /\ pc[j] = "r4a" /\ y = Null
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![j] = "r1"]
     \/
      /\ pc[j] = "r5"
      /\ y'  = j
      /\ UNCHANGED <<x, b>>
      /\ pc' = [pc EXCEPT ![j] = "r6"]
     \/
      /\ pc[j] = "r6" /\ x # j
      /\ b'  = [b EXCEPT ![j] = FALSE]
      /\ UNCHANGED <<x, y>>
      /\ pc' = [pc EXCEPT ![j] = "r8"]
     \/
      /\ pc[j] = "r6" /\ x = j
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![j] = "rcs"]
     \/
      /\ pc[j] = "r8"
      /\ \A k \in Proc: k = j \/ b[k] = FALSE
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![j] = "r9"]
     \/
      /\ pc[j] = "r9" /\ y # j /\ y = Null
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![j] = "r1"]
     \/
      /\ pc[j] = "r9" /\ y = j
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![j] = "rcs"]
     \/
      /\ pc[j] = "rcs"
      /\ UNCHANGED <<x, y, b>>
      /\ pc' = [pc EXCEPT ![j] = "rexit1"]
     \/
      /\ pc[j] = "rexit1"
      /\ y'  = Null
      /\ UNCHANGED <<x, b>>
      /\ pc' = [pc EXCEPT ![j] = "rexit2"]
     \/
      /\ pc[j] = "rexit2"
      /\ b'  = [b EXCEPT ![j] = FALSE]
      /\ UNCHANGED <<x, y>>
      /\ pc' = [pc EXCEPT ![j] = "r1"]
     )

LClass == \E i \in ProcL: StepL(i)
RClass == \E j \in ProcR: StepR(j)

Next == LClass \/ RClass

vars == <<x, y, b, pc>>

Spec == Init /\ [][Next]_vars /\ WF_vars(LClass) /\ WF_vars(RClass)

SomeProcessEntersInfinitelyOften == []<>(\E p \in Proc: InCS(p))

=============================================================================