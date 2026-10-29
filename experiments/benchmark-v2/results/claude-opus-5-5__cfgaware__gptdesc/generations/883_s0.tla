---------------------------- MODULE InnerSerial ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val, Reg, InitMem

VARIABLES regFile, opQ, opOrder

vars == <<regFile, opQ, opOrder>>

-----------------------------------------------------------------------------
NoVal == CHOOSE v : v \notin Val

RdRequest == [op : {"Rd"}, adr : Adr]
WrRequest == [op : {"Wr"}, adr : Adr, val : Val]
Request   == RdRequest \cup WrRequest

FreeRegValue == [op : {"Free"}, val : Val \cup {NoVal}]
RegValue     == FreeRegValue \cup Request

InitFree == [op |-> "Free", val |-> NoVal]

OpIdSet == [proc : Proc, idx : Nat]

InitWr == CHOOSE v : v \notin OpIdSet
NoSrc  == CHOOSE v : v \notin OpIdSet \cup {InitWr}
Done   == CHOOSE v : v \notin Reg

-----------------------------------------------------------------------------
OpIdOf(Q) == UNION { [proc : {p}, idx : DOMAIN Q[p]] : p \in Proc }

opId == OpIdOf(opQ)

opIdQ(oi) == opQ[oi.proc][oi.idx]

EntryOf(Q, oi) == Q[oi.proc][oi.idx]

IsWriteTo(Q, oi, a) ==
  /\ EntryOf(Q, oi).req.op = "Wr"
  /\ EntryOf(Q, oi).req.adr = a

IsIrreflexiveTransitive(R, S) ==
  /\ R \subseteq S \X S
  /\ \A x \in S : <<x, x>> \notin R
  /\ \A x, y, z \in S : (<<x, y>> \in R /\ <<y, z>> \in R) => <<x, z>> \in R

IsTotalOrder(T, S) ==
  /\ IsIrreflexiveTransitive(T, S)
  /\ \A x, y \in S : x /= y => (<<x, y>> \in T \/ <<y, x>> \in T)

ReadsFromOK(Q, T, ids) ==
  \A rd \in ids :
    LET e == EntryOf(Q, rd)
    IN  (e.req.op = "Rd" /\ e.source /= NoSrc) =>
          IF e.source = InitWr
            THEN \A w \in ids : IsWriteTo(Q, w, e.req.adr) => <<rd, w>> \in T
            ELSE /\ <<e.source, rd>> \in T
                 /\ \A w \in ids :
                      (IsWriteTo(Q, w, e.req.adr) /\ w /= e.source)
                        => (<<w, e.source>> \in T \/ <<rd, w>> \in T)

Legal(Q, R) ==
  LET ids == OpIdOf(Q)
  IN  /\ IsIrreflexiveTransitive(R, ids)
      /\ \E T \in SUBSET (ids \X ids) :
           /\ R \subseteq T
           /\ IsTotalOrder(T, ids)
           /\ \A o1, o2 \in ids :
                (o1.proc = o2.proc /\ o1.idx < o2.idx) => <<o1, o2>> \in T
           /\ ReadsFromOK(Q, T, ids)

-----------------------------------------------------------------------------
QEntry ==
  [req : Request, reg : Reg \cup {Done},
   source : OpIdSet \cup {InitWr, NoSrc}]

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegValue]]
  /\ opQ \in [Proc -> Seq(QEntry)]
  /\ opOrder \subseteq (opId \X opId)

-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> InitFree]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}

IssueRequest(p, req, r) ==
  /\ regFile[p][r].op = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> r, source |-> NoSrc])]
  /\ UNCHANGED opOrder

PendingIdx(p, r) == CHOOSE i \in DOMAIN opQ[p] : opQ[p][i].reg = r

RespondToWr(p, r) ==
  /\ regFile[p][r].op = "Wr"
  /\ \E i \in DOMAIN opQ[p] : opQ[p][i].reg = r
  /\ LET i == PendingIdx(p, r)
     IN  /\ regFile' = [regFile EXCEPT ![p][r] = InitFree]
         /\ opQ' = [opQ EXCEPT ![p][i].reg = Done]
         /\ \E R \in SUBSET (opId \X opId) :
              /\ opOrder \subseteq R
              /\ Legal(opQ', R)
              /\ opOrder' = R

RespondToRd(p, r) ==
  /\ regFile[p][r].op = "Rd"
  /\ \E i \in DOMAIN opQ[p] : opQ[p][i].reg = r
  /\ LET i  == PendingIdx(p, r)
         a  == opQ[p][i].req.adr
     IN  \E src \in {InitWr} \cup {w \in opId : IsWriteTo(opQ, w, a)} :
           LET v == IF src = InitWr THEN InitMem[a] ELSE opIdQ(src).req.val
           IN  /\ regFile' = [regFile EXCEPT ![p][r] =
                                [op |-> "Free", val |-> v]]
               /\ opQ' = [opQ EXCEPT ![p][i].reg = Done,
                                     ![p][i].source = src]
               /\ \E R \in SUBSET (opId \X opId) :
                    /\ opOrder \subseteq R
                    /\ Legal(opQ', R)
                    /\ opOrder' = R

Internal ==
  /\ UNCHANGED <<regFile, opQ>>
  /\ \E R \in SUBSET (opId \X opId) :
       /\ opOrder \subseteq R
       /\ opOrder /= R
       /\ Legal(opQ, R)
       /\ opOrder' = R

OrderPair ==
  /\ UNCHANGED <<regFile, opQ>>
  /\ \E oi, oj \in opId :
       /\ oi /= oj
       /\ <<oi, oj>> \notin opOrder
       /\ <<oj, oi>> \notin opOrder
       /\ \E R \in SUBSET (opId \X opId) :
            /\ opOrder \subseteq R
            /\ Legal(opQ, R)
            /\ (<<oi, oj>> \in R \/ <<oj, oi>> \in R)
            /\ opOrder' = R

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : IssueRequest(p, req, r)
  \/ \E p \in Proc, r \in Reg : RespondToWr(p, r) \/ RespondToRd(p, r)
  \/ Internal

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc, r \in Reg :
        /\ WF_vars(RespondToWr(p, r))
        /\ WF_vars(RespondToRd(p, r))
  /\ WF_vars(OrderPair)

=============================================================================