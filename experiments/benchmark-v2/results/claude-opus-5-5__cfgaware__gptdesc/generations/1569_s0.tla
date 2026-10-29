------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ MaxNum \in Nat

Procs == 1..NumProcs

a \prec b == \/ a[1] < b[1]
             \/ (a[1] = b[1]) /\ (a[2] < b[2])

(***************************************************************************
--algorithm Bakery
variables num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
process (p \in Procs)
  variables unread = {}, max = 0, nxt = 1;
{
p1: while (TRUE) {
      unread := Procs \ {self};
      max := 0;
      flag[self] := TRUE;
p2:   while (unread # {}) {
        with (i \in unread) {
          if (num[i] > max) { max := num[i] };
          unread := unread \ {i}
        }
      };
p3:   num[self] := max + 1;
p4:   flag[self] := FALSE;
      unread := Procs \ {self};
p5:   while (unread # {}) {
        with (i \in unread) { nxt := i };
        await ~ flag[nxt];
p6:     await \/ num[nxt] = 0
              \/ <<num[self], self>> \prec <<num[nxt], nxt>>;
        unread := unread \ {nxt}
      };
cs:   skip;
p7:   num[self] := 0
    }
}
end algorithm
***************************************************************************)

VARIABLES num, flag, pc, unread, max, nxt

vars == << num, flag, pc, unread, max, nxt >>

ProcSet == Procs

Init == /\ num = [i \in Procs |-> 0]
        /\ flag = [i \in Procs |-> FALSE]
        /\ unread = [self \in Procs |-> {}]
        /\ max = [self \in Procs |-> 0]
        /\ nxt = [self \in Procs |-> 1]
        /\ pc = [self \in ProcSet |-> "p1"]

p1(self) == /\ pc[self] = "p1"
            /\ unread' = [unread EXCEPT ![self] = Procs \ {self}]
            /\ max' = [max EXCEPT ![self] = 0]
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << num, nxt >>

p2(self) == /\ pc[self] = "p2"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            /\ IF num[i] > max[self]
                                  THEN max' = [max EXCEPT ![self] = num[i]]
                                  ELSE max' = max
                            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {i}]
                       /\ pc' = [pc EXCEPT ![self] = "p2"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p3"]
                       /\ UNCHANGED << unread, max >>
            /\ UNCHANGED << num, flag, nxt >>

p3(self) == /\ pc[self] = "p3"
            /\ num' = [num EXCEPT ![self] = max[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p4(self) == /\ pc[self] = "p4"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ unread' = [unread EXCEPT ![self] = Procs \ {self}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, max, nxt >>

p5(self) == /\ pc[self] = "p5"
            /\ IF unread[self] # {}
                  THEN /\ \E i \in unread[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       /\ ~ flag[nxt'[self]]
                       /\ pc' = [pc EXCEPT ![self] = "p6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                       /\ nxt' = nxt
            /\ UNCHANGED << num, flag, unread, max >>

p6(self) == /\ pc[self] = "p6"
            /\ \/ num[nxt[self]] = 0
               \/ <<num[self], self>> \prec <<num[nxt[self]], nxt[self]>>
            /\ unread' = [unread EXCEPT ![self] = unread[self] \ {nxt[self]}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << num, flag, max, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p7"]
            /\ UNCHANGED << num, flag, unread, max, nxt >>

p7(self) == /\ pc[self] = "p7"
            /\ num' = [num EXCEPT ![self] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << flag, unread, max, nxt >>

p(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self)
              \/ p5(self) \/ p6(self) \/ cs(self) \/ p7(self)

Next == \E self \in Procs : p(self)

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unread \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"p1","p2","p3","p4","p5","p6","cs","p7"}]

MutualExclusion == \A i, j \in Procs :
                      (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Invariant == MutualExclusion

Constraint == \A i \in Procs : num[i] <= MaxNum

=============================================================================