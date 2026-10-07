---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ M \in Nat /\ N \in Nat
       /\ 1 <= M /\ M < N

ProcA == 1..M
ProcB == (M+1)..N
Proc  == 1..N

VARIABLES x, y, b, pc

Vars == << x, y, b, pc >>

TypeInv ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [ Proc ->
               {"A0","A2","AwaitY0A","A3","A4","WaitAllFalseA","A5","AwaitY0A2",
                "cs","A6",
                "B0","B2","AwaitY0B","B3","B4","WaitAllFalseB","B5","AwaitY0B2","B6"} ]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> IF i \in ProcA THEN "A0" ELSE "B0"]
  /\ TypeInv

(***************************************************************************)
(* Class A process actions                                                  *)
(***************************************************************************)
A0(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A0"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "A2"]
  /\ UNCHANGED y

A2_block(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A2"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "AwaitY0A"]
  /\ UNCHANGED <<x, y>>

A2_fast(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A2"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "A3"]
  /\ UNCHANGED <<x, y, b>>

AwaitY0A(i) ==
  /\ i \in ProcA
  /\ pc[i] = "AwaitY0A"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "A0"]
  /\ UNCHANGED <<x, y, b>>

A3(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A3"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "A4"]
  /\ UNCHANGED <<x, b>>

A4_do(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A4"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "WaitAllFalseA"]
  /\ UNCHANGED <<x, y>>

A4_skip(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A4"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<x, y, b>>

WaitAllFalseA(i) ==
  /\ i \in ProcA
  /\ pc[i] = "WaitAllFalseA"
  /\ \A j \in Proc: b[j] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "A5"]
  /\ UNCHANGED <<x, y, b>>

A5_toCS(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A5"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<x, y, b>>

A5_toAwait2(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A5"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "AwaitY0A2"]
  /\ UNCHANGED <<x, y, b>>

AwaitY0A2(i) ==
  /\ i \in ProcA
  /\ pc[i] = "AwaitY0A2"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "A0"]
  /\ UNCHANGED <<x, y, b>>

Acs(i) ==
  /\ i \in ProcA
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "A6"]
  /\ UNCHANGED <<x, y, b>>

A6(i) ==
  /\ i \in ProcA
  /\ pc[i] = "A6"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "A0"]
  /\ UNCHANGED x

ProcAStep(i) ==
  A0(i) \/ A2_block(i) \/ A2_fast(i) \/ AwaitY0A(i) \/
  A3(i) \/ A4_do(i) \/ A4_skip(i) \/ WaitAllFalseA(i) \/
  A5_toCS(i) \/ A5_toAwait2(i) \/ AwaitY0A2(i) \/
  Acs(i) \/ A6(i)

(***************************************************************************)
(* Class B process actions                                                  *)
(***************************************************************************)
B0(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B0"
  /\ x' = j
  /\ b' = [b EXCEPT ![j] = TRUE]
  /\ pc' = [pc EXCEPT ![j] = "B2"]
  /\ UNCHANGED y

B2_block(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B2"
  /\ y # 0
  /\ b' = [b EXCEPT ![j] = FALSE]
  /\ pc' = [pc EXCEPT ![j] = "AwaitY0B"]
  /\ UNCHANGED <<x, y>>

B2_fast(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B2"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![j] = "B3"]
  /\ UNCHANGED <<x, y, b>>

AwaitY0B(j) ==
  /\ j \in ProcB
  /\ pc[j] = "AwaitY0B"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![j] = "B0"]
  /\ UNCHANGED <<x, y, b>>

B3(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B3"
  /\ y' = j
  /\ pc' = [pc EXCEPT ![j] = "B4"]
  /\ UNCHANGED <<x, b>>

B4_do(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B4"
  /\ x # j
  /\ b' = [b EXCEPT ![j] = FALSE]
  /\ pc' = [pc EXCEPT ![j] = "WaitAllFalseB"]
  /\ UNCHANGED <<x, y>>

B4_skip(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B4"
  /\ x = j
  /\ pc' = [pc EXCEPT ![j] = "cs"]
  /\ UNCHANGED <<x, y, b>>

WaitAllFalseB(j) ==
  /\ j \in ProcB
  /\ pc[j] = "WaitAllFalseB"
  /\ \A k \in Proc: b[k] = FALSE
  /\ pc' = [pc EXCEPT ![j] = "B5"]
  /\ UNCHANGED <<x, y, b>>

B5_toCS(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B5"
  /\ y = j
  /\ pc' = [pc EXCEPT ![j] = "cs"]
  /\ UNCHANGED <<x, y, b>>

B5_toAwait2(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B5"
  /\ y # j
  /\ pc' = [pc EXCEPT ![j] = "AwaitY0B2"]
  /\ UNCHANGED <<x, y, b>>

AwaitY0B2(j) ==
  /\ j \in ProcB
  /\ pc[j] = "AwaitY0B2"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![j] = "B0"]
  /\ UNCHANGED <<x, y, b>>

Bcs(j) ==
  /\ j \in ProcB
  /\ pc[j] = "cs"
  /\ pc' = [pc EXCEPT ![j] = "B6"]
  /\ UNCHANGED <<x, y, b>>

B6(j) ==
  /\ j \in ProcB
  /\ pc[j] = "B6"
  /\ y' = 0
  /\ b' = [b EXCEPT ![j] = FALSE]
  /\ pc' = [pc EXCEPT ![j] = "B0"]
  /\ UNCHANGED x

ProcBStep(j) ==
  B0(j) \/ B2_block(j) \/ B2_fast(j) \/ AwaitY0B(j) \/
  B3(j) \/ B4_do(j) \/ B4_skip(j) \/ WaitAllFalseB(j) \/
  B5_toCS(j) \/ B5_toAwait2(j) \/ AwaitY0B2(j) \/
  Bcs(j) \/ B6(j)

Next ==
  ( \E i \in ProcA: ProcAStep(i) )
  \/ ( \E j \in ProcB: ProcBStep(j) )

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ (\A i \in ProcA: WF_Vars(ProcAStep(i)))
  /\ (\A j \in ProcB: WF_Vars(ProcBStep(j)))

InCS(p) == p \in Proc /\ pc[p] = "cs"

MutualExclusion ==
  \A p \in Proc: \A q \in Proc:
    (p # q) => ~(InCS(p) /\ InCS(q))

Liveness ==
  []<>(\E p \in Proc: InCS(p))
==============================