---------------------------- MODULE DCASDeque ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS defaultInitValue, Val, Address, Dummy, Procs, null, GC

Nodes == Address \cup {Dummy}
Sides == {"L", "R"}
Opp(d) == IF d = "L" THEN "R" ELSE "L"

VARIABLES
  mem,        \* mem[n] = [L |-> node, R |-> node, V |-> value]
  freeList,   \* set of free addresses
  Hat,        \* Hat["L"] = LeftHat, Hat["R"] = RightHat
  pc, op, dir, v, nd, h, oh, t, status, rval, expected,
  q,          \* abstract deque (linearization)
  wasEmpty    \* wasEmpty[p]: abstract deque was empty during p's current op

vars == <<mem, freeList, Hat, pc, op, dir, v, nd, h, oh, t,
          status, rval, expected, q, wasEmpty>>

procLocals == <<op, dir, v, nd, h, oh, t, status, rval, expected>>

Symmetry == Permutations(Address \ {Dummy}) \cup Permutations(Procs)

Init ==
  /\ mem = [n \in Nodes |-> [L |-> Dummy, R |-> Dummy, V |-> null]]
  /\ freeList = Address \ {Dummy}
  /\ Hat = [s \in Sides |-> Dummy]
  /\ pc = [p \in Procs |-> "Start"]
  /\ op = [p \in Procs |-> defaultInitValue]
  /\ dir = [p \in Procs |-> defaultInitValue]
  /\ v = [p \in Procs |-> defaultInitValue]
  /\ nd = [p \in Procs |-> defaultInitValue]
  /\ h = [p \in Procs |-> defaultInitValue]
  /\ oh = [p \in Procs |-> defaultInitValue]
  /\ t = [p \in Procs |-> defaultInitValue]
  /\ status = [p \in Procs |-> defaultInitValue]
  /\ rval = [p \in Procs |-> defaultInitValue]
  /\ expected = [p \in Procs |-> defaultInitValue]
  /\ q = << >>
  /\ wasEmpty = [p \in Procs |-> TRUE]

PushAbs(d, x) == IF d = "R" THEN Append(q, x) ELSE <<x>> \o q
PopAbs(d) == IF Len(q) = 0 THEN q
             ELSE IF d = "R" THEN SubSeq(q, 1, Len(q) - 1) ELSE Tail(q)
PopVal(d) == IF Len(q) = 0 THEN null
             ELSE IF d = "R" THEN q[Len(q)] ELSE Head(q)

\* ---------------- Test harness: choose random operation ----------------
Start(p) ==
  /\ pc[p] = "Start"
  /\ \E o \in {"push", "pop"}, d \in Sides, x \in Val :
       /\ op' = [op EXCEPT ![p] = o]
       /\ dir' = [dir EXCEPT ![p] = d]
       /\ v' = [v EXCEPT ![p] = IF o = "push" THEN x ELSE defaultInitValue]
       /\ pc' = [pc EXCEPT ![p] = IF o = "push" THEN "A1" ELSE "B1"]
  /\ UNCHANGED <<mem, freeList, Hat, nd, h, oh, t, status, rval, expected, q>>

Ret(p) ==
  /\ pc[p] = "Ret"
  /\ pc' = [pc EXCEPT ![p] = "Start"]
  /\ op' = [op EXCEPT ![p] = defaultInitValue]
  /\ dir' = [dir EXCEPT ![p] = defaultInitValue]
  /\ v' = [v EXCEPT ![p] = defaultInitValue]
  /\ nd' = [nd EXCEPT ![p] = defaultInitValue]
  /\ h' = [h EXCEPT ![p] = defaultInitValue]
  /\ oh' = [oh EXCEPT ![p] = defaultInitValue]
  /\ t' = [t EXCEPT ![p] = defaultInitValue]
  /\ status' = [status EXCEPT ![p] = defaultInitValue]
  /\ rval' = [rval EXCEPT ![p] = defaultInitValue]
  /\ expected' = [expected EXCEPT ![p] = defaultInitValue]
  /\ UNCHANGED <<mem, freeList, Hat, q>>

\* ---------------- Push (side dir[p]) ----------------
A1(p) ==
  /\ pc[p] = "A1"
  /\ IF freeList = {}
       THEN /\ status' = [status EXCEPT ![p] = "full"]
            /\ pc' = [pc EXCEPT ![p] = "Ret"]
            /\ UNCHANGED <<freeList, nd>>
       ELSE \E a \in freeList :
            /\ freeList' = freeList \ {a}
            /\ nd' = [nd EXCEPT ![p] = a]
            /\ pc' = [pc EXCEPT ![p] = "A2"]
            /\ UNCHANGED status
  /\ UNCHANGED <<mem, Hat, op, dir, v, h, oh, t, rval, expected, q>>

A2(p) ==
  /\ pc[p] = "A2"
  /\ mem' = [mem EXCEPT ![nd[p]][dir[p]] = Dummy, ![nd[p]].V = v[p]]
  /\ pc' = [pc EXCEPT ![p] = "A3"]
  /\ UNCHANGED <<freeList, Hat, procLocals, q>>

A3(p) ==
  /\ pc[p] = "A3"
  /\ h' = [h EXCEPT ![p] = Hat[dir[p]]]
  /\ pc' = [pc EXCEPT ![p] = "A4"]
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, oh, t, status, rval, expected, q>>

A4(p) ==
  /\ pc[p] = "A4"
  /\ t' = [t EXCEPT ![p] = mem[h[p]][dir[p]]]
  /\ pc' = [pc EXCEPT ![p] = "A5"]
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, h, oh, status, rval, expected, q>>

A5(p) ==
  /\ pc[p] = "A5"
  /\ IF t[p] = h[p]
       THEN /\ mem' = [mem EXCEPT ![nd[p]][Opp(dir[p])] = Dummy]
            /\ pc' = [pc EXCEPT ![p] = "A6"]
       ELSE /\ mem' = [mem EXCEPT ![nd[p]][Opp(dir[p])] = h[p]]
            /\ pc' = [pc EXCEPT ![p] = "A8"]
  /\ UNCHANGED <<freeList, Hat, procLocals, q>>

A6(p) ==
  /\ pc[p] = "A6"
  /\ oh' = [oh EXCEPT ![p] = Hat[Opp(dir[p])]]
  /\ pc' = [pc EXCEPT ![p] = "A7"]
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, h, t, status, rval, expected, q>>

\* DCAS(&Hat[d], &Hat[Opp d], h, oh, nd, nd)
A7(p) ==
  /\ pc[p] = "A7"
  /\ IF Hat[dir[p]] = h[p] /\ Hat[Opp(dir[p])] = oh[p]
       THEN /\ Hat' = [s \in Sides |-> nd[p]]
            /\ q' = PushAbs(dir[p], v[p])
            /\ status' = [status EXCEPT ![p] = "okay"]
            /\ pc' = [pc EXCEPT ![p] = "Ret"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "A3"]
            /\ UNCHANGED <<Hat, q, status>>
  /\ UNCHANGED <<mem, freeList, op, dir, v, nd, h, oh, t, rval, expected>>

\* DCAS(&Hat[d], &h->d, h, t, nd, nd)
A8(p) ==
  /\ pc[p] = "A8"
  /\ IF Hat[dir[p]] = h[p] /\ mem[h[p]][dir[p]] = t[p]
       THEN /\ Hat' = [Hat EXCEPT ![dir[p]] = nd[p]]
            /\ mem' = [mem EXCEPT ![h[p]][dir[p]] = nd[p]]
            /\ q' = PushAbs(dir[p], v[p])
            /\ status' = [status EXCEPT ![p] = "okay"]
            /\ pc' = [pc EXCEPT ![p] = "Ret"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "A3"]
            /\ UNCHANGED <<Hat, mem, q, status>>
  /\ UNCHANGED <<freeList, op, dir, v, nd, h, oh, t, rval, expected>>

\* ---------------- Pop (side dir[p]) ----------------
B1(p) ==
  /\ pc[p] = "B1"
  /\ h' = [h EXCEPT ![p] = Hat[dir[p]]]
  /\ pc' = [pc EXCEPT ![p] = "B2"]
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, oh, t, status, rval, expected, q>>

B2(p) ==
  /\ pc[p] = "B2"
  /\ oh' = [oh EXCEPT ![p] = Hat[Opp(dir[p])]]
  /\ pc' = [pc EXCEPT ![p] = "B3"]
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, h, t, status, rval, expected, q>>

B3(p) ==
  /\ pc[p] = "B3"
  /\ IF mem[h[p]][dir[p]] = h[p]
       THEN /\ status' = [status EXCEPT ![p] = "empty"]
            /\ pc' = [pc EXCEPT ![p] = "Ret"]
       ELSE /\ pc' = [pc EXCEPT ![p] = IF h[p] = oh[p] THEN "B4" ELSE "B5"]
            /\ UNCHANGED status
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, h, oh, t, rval, expected, q>>

\* DCAS(&Hat[d], &Hat[Opp d], h, oh, Dummy, Dummy)
B4(p) ==
  /\ pc[p] = "B4"
  /\ IF Hat[dir[p]] = h[p] /\ Hat[Opp(dir[p])] = oh[p]
       THEN /\ Hat' = [s \in Sides |-> Dummy]
            /\ expected' = [expected EXCEPT ![p] = PopVal(dir[p])]
            /\ q' = PopAbs(dir[p])
            /\ pc' = [pc EXCEPT ![p] = "B7"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "B1"]
            /\ UNCHANGED <<Hat, expected, q>>
  /\ UNCHANGED <<mem, freeList, op, dir, v, nd, h, oh, t, status, rval>>

B5(p) ==
  /\ pc[p] = "B5"
  /\ t' = [t EXCEPT ![p] = mem[h[p]][Opp(dir[p])]]
  /\ pc' = [pc EXCEPT ![p] = "B6"]
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, h, oh, status, rval, expected, q>>

\* DCAS(&Hat[d], &h->Opp(d), h, t, t, h)
B6(p) ==
  /\ pc[p] = "B6"
  /\ IF Hat[dir[p]] = h[p] /\ mem[h[p]][Opp(dir[p])] = t[p]
       THEN /\ Hat' = [Hat EXCEPT ![dir[p]] = t[p]]
            /\ mem' = [mem EXCEPT ![h[p]][Opp(dir[p])] = h[p]]
            /\ expected' = [expected EXCEPT ![p] = PopVal(dir[p])]
            /\ q' = PopAbs(dir[p])
            /\ pc' = [pc EXCEPT ![p] = "B8"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "B1"]
            /\ UNCHANGED <<Hat, mem, expected, q>>
  /\ UNCHANGED <<freeList, op, dir, v, nd, h, oh, t, status, rval>>

B7(p) ==
  /\ pc[p] = "B7"
  /\ rval' = [rval EXCEPT ![p] = mem[h[p]].V]
  /\ status' = [status EXCEPT ![p] = "okay"]
  /\ pc' = [pc EXCEPT ![p] = "Ret"]
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, h, oh, t, expected, q>>

B8(p) ==
  /\ pc[p] = "B8"
  /\ rval' = [rval EXCEPT ![p] = mem[h[p]].V]
  /\ pc' = [pc EXCEPT ![p] = "B9"]
  /\ UNCHANGED <<mem, freeList, Hat, op, dir, v, nd, h, oh, t, status, expected, q>>

B9(p) ==
  /\ pc[p] = "B9"
  /\ mem' = [mem EXCEPT ![h[p]][dir[p]] = Dummy]
  /\ status' = [status EXCEPT ![p] = "okay"]
  /\ pc' = [pc EXCEPT ![p] = "Ret"]
  /\ UNCHANGED <<freeList, Hat, op, dir, v, nd, h, oh, t, rval, expected, q>>

Step(p) ==
  \/ Start(p) \/ Ret(p)
  \/ A1(p) \/ A2(p) \/ A3(p) \/ A4(p) \/ A5(p) \/ A6(p) \/ A7(p) \/ A8(p)
  \/ B1(p) \/ B2(p) \/ B3(p) \/ B4(p) \/ B5(p) \/ B6(p) \/ B7(p) \/ B8(p) \/ B9(p)

\* ---------------- Garbage collection ----------------
Reachable ==
  LET Grow(S) == S \cup {mem[x][f] : x \in S, f \in Sides}
      R[n \in Nat] == IF n = 0 THEN {Hat["L"], Hat["R"]} ELSE Grow(R[n-1])
  IN  R[Cardinality(Nodes)]

Referenced ==
  {nd[p] : p \in Procs} \cup {h[p] : p \in Procs}
    \cup {oh[p] : p \in Procs} \cup {t[p] : p \in Procs}

Collect ==
  /\ GC
  /\ \E a \in Address \ ({Dummy} \cup freeList) :
       /\ a \notin Reachable
       /\ a \notin Referenced
       /\ freeList' = freeList \cup {a}
       /\ mem' = [mem EXCEPT ![a] = [L |-> Dummy, R |-> Dummy, V |-> null]]
  /\ UNCHANGED <<Hat, pc, procLocals, q, wasEmpty>>

Next ==
  \/ \E p \in Procs :
       /\ Step(p)
       /\ wasEmpty' = [r \in Procs |->
                        (IF r = p /\ pc[p] = "Start" THEN FALSE ELSE wasEmpty[r])
                        \/ q' = << >>]
  \/ Collect

Spec == Init /\ [][Next]_vars

\* ---------------- Correctness properties ----------------
TypeOK ==
  /\ Hat \in [Sides -> Nodes]
  /\ freeList \subseteq Address
  /\ mem \in [Nodes -> [L : Nodes, R : Nodes, V : Val \cup {null}]]

\* Popped values equal the abstract deque's end at the linearization point
\* (no lost values, no duplicates); "empty" only when the deque was empty.
Linearizable ==
  \A p \in Procs :
    (pc[p] = "Ret" /\ op[p] = "pop") =>
      IF status[p] = "empty" THEN wasEmpty[p]
                             ELSE rval[p] = expected[p] /\ rval[p] \in Val

NoFullUnlessExhausted ==
  \A p \in Procs : (pc[p] = "Ret" /\ status[p] = "full") => op[p] = "push"
=============================================================================