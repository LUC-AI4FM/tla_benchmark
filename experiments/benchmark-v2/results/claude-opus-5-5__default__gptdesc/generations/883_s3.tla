---------------------------- MODULE InnerSerial ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          InitVal,   \* initial value of every address
          MaxOps     \* bound on number of operations issued per process

ASSUME /\ InitVal \in Val
       /\ MaxOps \in Nat

VARIABLES opQ,      \* opQ[p] : sequence of operations issued by process p
          opOrder   \* partial order relation over operation identifiers

vars == <<opQ, opOrder>>

-----------------------------------------------------------------------------
NoVal   == CHOOSE v : v \notin Val
InitSrc == "InitWrite"
NoSrc   == "NoSource"

OpId == {<<p, i>> : p \in Proc, i \in 1..MaxOps}

Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

Entry == [req : Request, done : BOOLEAN, val : Val \cup {NoVal},
          src : OpId \cup {InitSrc, NoSrc}]

\* Helpers parameterized by a queue function Q
IdsOf(Q) == UNION { {<<p, i>> : i \in 1..Len(Q[p])} : p \in Proc }

OpOf(Q, o) == Q[o[1]][o[2]]

IsWrite(Q, o) == OpOf(Q, o).req.op = "Wr"

DoneIds(Q) == {o \in IdsOf(Q) : OpOf(Q, o).done}

DoneReads(Q) == {o \in DoneIds(Q) : ~IsWrite(Q, o)}

ProgOrder(Q, S) == {pr \in S \X S : /\ pr[1][1] = pr[2][1]
                                   /\ pr[1][2] < pr[2][2]}

IsTotalOrder(T, S) ==
  /\ \A a \in S : <<a, a>> \notin T
  /\ \A a, b \in S : a # b => (<<a, b>> \in T \/ <<b, a>> \in T)
  /\ \A a, b, c \in S : (<<a, b>> \in T /\ <<b, c>> \in T) => <<a, c>> \in T

\* A completed read r is legal w.r.t. total order T if it reads the value of
\* the last write to its address preceding it in T (or the initial value).
LegalRead(Q, r, T, S) ==
  LET a   == OpOf(Q, r).req.adr
      s   == OpOf(Q, r).src
      Wrs == {w \in S : IsWrite(Q, w) /\ OpOf(Q, w).req.adr = a}
  IN  IF s = InitSrc
        THEN \A w \in Wrs : <<r, w>> \in T
        ELSE /\ s \in Wrs
             /\ <<s, r>> \in T
             /\ \A w \in Wrs \ {s} : ~(<<s, w>> \in T /\ <<w, r>> \in T)

\* The history Q with order ord can be extended to a total order consistent
\* with program order, ord, and the read-from constraints.
Serializable(Q, ord) ==
  LET S == IdsOf(Q)
  IN  \E T \in SUBSET (S \X S) :
        /\ IsTotalOrder(T, S)
        /\ (ord \cap (S \X S)) \subseteq T
        /\ ProgOrder(Q, S) \subseteq T
        /\ \A r \in DoneReads(Q) : LegalRead(Q, r, T, S)

IssuedIds == IdsOf(opQ)

-----------------------------------------------------------------------------
TypeOK ==
  /\ opQ \in [Proc -> Seq(Entry)]
  /\ \A p \in Proc : Len(opQ[p]) <= MaxOps
  /\ opOrder \subseteq (IssuedIds \X IssuedIds)

Init ==
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}

\* Issue a new request; a process has at most one outstanding request.
Issue(p, req) ==
  LET n == Len(opQ[p]) + 1
  IN  /\ Len(opQ[p]) < MaxOps
      /\ Len(opQ[p]) = 0 \/ opQ[p][Len(opQ[p])].done
      /\ opQ' = [opQ EXCEPT ![p] =
                   Append(@, [req |-> req, done |-> FALSE,
                              val |-> NoVal, src |-> NoSrc])]
      /\ opOrder' = opOrder \cup { << <<p, j>>, <<p, n>> >> : j \in 1..(n - 1) }

\* Respond to a pending write request.
RespondWr(p) ==
  LET n == Len(opQ[p])
  IN  /\ n > 0
      /\ ~opQ[p][n].done
      /\ opQ[p][n].req.op = "Wr"
      /\ opQ' = [opQ EXCEPT ![p][n].done = TRUE]
      /\ Serializable(opQ', opOrder)
      /\ UNCHANGED opOrder

\* Respond to a pending read request, recording the source write.
RespondRd(p) ==
  LET n   == Len(opQ[p])
      me  == <<p, n>>
  IN  /\ n > 0
      /\ ~opQ[p][n].done
      /\ opQ[p][n].req.op = "Rd"
      /\ \E s \in {InitSrc} \cup
                  {w \in IssuedIds : /\ IsWrite(opQ, w)
                                     /\ OpOf(opQ, w).req.adr = opQ[p][n].req.adr
                                     /\ w # me} :
           LET v    == IF s = InitSrc THEN InitVal ELSE OpOf(opQ, s).req.val
               newQ == [opQ EXCEPT ![p][n].done = TRUE,
                                   ![p][n].val  = v,
                                   ![p][n].src  = s]
               newO == IF s = InitSrc THEN opOrder
                                      ELSE opOrder \cup { <<s, me>> }
           IN  /\ Serializable(newQ, newO)
               /\ opQ' = newQ
               /\ opOrder' = newO

\* Internal step: only extends the order relation by comparing two
\* distinct, currently incomparable operations.
Internal ==
  /\ \E a, b \in IssuedIds :
       /\ a # b
       /\ <<a, b>> \notin opOrder
       /\ <<b, a>> \notin opOrder
       /\ opOrder' = opOrder \cup { <<a, b>> }
       /\ Serializable(opQ, opOrder')
  /\ UNCHANGED opQ

Next ==
  \/ \E p \in Proc, req \in Request : Issue(p, req)
  \/ \E p \in Proc : RespondWr(p)
  \/ \E p \in Proc : RespondRd(p)
  \/ Internal

Fairness ==
  /\ \A p \in Proc : WF_vars(RespondWr(p))
  /\ \A p \in Proc : WF_vars(RespondRd(p))
  /\ WF_vars(Internal)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety invariants
OrderOnIssued == opOrder \subseteq (IssuedIds \X IssuedIds)

ProgramOrderIncluded == ProgOrder(opQ, IssuedIds) \subseteq opOrder

ReadFromIncluded ==
  \A r \in DoneReads(opQ) :
    OpOf(opQ, r).src # InitSrc => <<OpOf(opQ, r).src, r>> \in opOrder

ReadValueCorrect ==
  \A r \in DoneReads(opQ) :
    OpOf(opQ, r).val = IF OpOf(opQ, r).src = InitSrc
                         THEN InitVal
                         ELSE OpOf(opQ, OpOf(opQ, r).src).req.val

SerializableInv == Serializable(opQ, opOrder)

\* Liveness properties
ResponseLiveness ==
  \A p \in Proc : \A i \in 1..MaxOps :
    [](i <= Len(opQ[p]) => <>(opQ[p][i].done))

OrderLiveness ==
  \A a, b \in OpId :
    []((a \in IssuedIds /\ b \in IssuedIds /\ a # b)
         => <>(<<a, b>> \in opOrder \/ <<b, a>> \in opOrder))

THEOREM Spec => [](TypeOK /\ OrderOnIssued /\ ProgramOrderIncluded /\
                   ReadFromIncluded /\ ReadValueCorrect /\ SerializableInv)
THEOREM Spec => ResponseLiveness /\ OrderLiveness
=============================================================================