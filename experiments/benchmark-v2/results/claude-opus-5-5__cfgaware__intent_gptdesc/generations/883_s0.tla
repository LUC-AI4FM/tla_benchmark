------------------------------ MODULE SerialRegisterService ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc,      \* set of clients
          Adr,       \* finite set of register addresses
          Val,       \* set of data values
          InitMem,   \* initial memory: a function Adr -> Val
          InitWr,    \* special "initial write" source marker
          Done       \* marker for a completed queue entry

ASSUME InitMem \in [Adr -> Val]

VARIABLES
  opQ,      \* opQ[p]   : per-client FIFO of requests (or Done)
  opIdQ,    \* opIdQ[p] : identifiers of the entries in opQ[p]
  opId,     \* opId[p]  : number of operations issued so far by p
  opLog,    \* function from issued op identifiers to their requests
  opOrder,  \* recorded partial order on op identifiers
  source,   \* function from completed reads to their chosen source
  result    \* function from completed reads to the value returned

vars == <<opQ, opIdQ, opId, opLog, opOrder, source, result>>

-----------------------------------------------------------------------------
Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

QLen == Cardinality(Adr)

EmptyFcn == [x \in {} |-> InitWr]

IsPending(e) == e # Done

Writes(log, a) == {w \in DOMAIN log : log[w].op = "Wr" /\ log[w].adr = a}

Orders(S) == { f \in [1..Cardinality(S) -> S] :
                 \A i, j \in DOMAIN f : i # j => f[i] # f[j] }

\* The recorded state can be extended to a total (serial) order.
Serializable(log, ord, src) ==
  \E f \in Orders(DOMAIN log) :
    LET P(a) == CHOOSE i \in DOMAIN f : f[i] = a
    IN  /\ \A pr \in ord : P(pr[1]) < P(pr[2])
        /\ \A a, b \in DOMAIN log :
              (a[1] = b[1] /\ a[2] < b[2]) => P(a) < P(b)
        /\ \A r \in DOMAIN src :
              LET s   == src[r]
                  Wrs == Writes(log, log[r].adr)
              IN  IF s = InitWr
                    THEN \A w \in Wrs : P(r) < P(w)
                    ELSE /\ s \in Wrs
                         /\ P(s) < P(r)
                         /\ \A w \in Wrs \ {s} : P(w) < P(s) \/ P(r) < P(w)

SrcVal(log, r, s) == IF s = InitWr THEN InitMem[log[r].adr] ELSE log[s].val

SlotFree(p, a) ==
  \A i \in 1..Len(opQ[p]) : ~IsPending(opQ[p][i]) \/ opQ[p][i].adr # a

-----------------------------------------------------------------------------
Init ==
  /\ opQ     = [p \in Proc |-> << >>]
  /\ opIdQ   = [p \in Proc |-> << >>]
  /\ opId    = [p \in Proc |-> 0]
  /\ opLog   = EmptyFcn
  /\ opOrder = {}
  /\ source  = EmptyFcn
  /\ result  = EmptyFcn

Issue(p, req) ==
  /\ SlotFree(p, req.adr)
  /\ Len(opQ[p]) < QLen
  /\ LET id == <<p, opId[p] + 1>>
     IN  /\ opId'  = [opId EXCEPT ![p] = @ + 1]
         /\ opQ'   = [opQ EXCEPT ![p] = Append(@, req)]
         /\ opIdQ' = [opIdQ EXCEPT ![p] = Append(@, id)]
         /\ opLog' = opLog @@ (id :> req)
  /\ UNCHANGED <<opOrder, source, result>>

RespondWr(p, i) ==
  /\ i \in 1..Len(opQ[p])
  /\ IsPending(opQ[p][i])
  /\ opQ[p][i].op = "Wr"
  /\ opQ' = [opQ EXCEPT ![p][i] = Done]
  /\ UNCHANGED <<opIdQ, opId, opLog, opOrder, source, result>>

RespondRd(p, i) ==
  /\ i \in 1..Len(opQ[p])
  /\ IsPending(opQ[p][i])
  /\ opQ[p][i].op = "Rd"
  /\ LET id == opIdQ[p][i]
     IN  \E s \in {InitWr} \cup (Writes(opLog, opQ[p][i].adr) \ {id}) :
           LET newSrc == source @@ (id :> s)
               newOrd == IF s = InitWr THEN opOrder ELSE opOrder \cup {<<s, id>>}
           IN  /\ Serializable(opLog, newOrd, newSrc)
               /\ source'  = newSrc
               /\ opOrder' = newOrd
               /\ result'  = result @@ (id :> SrcVal(opLog, id, s))
               /\ opQ'     = [opQ EXCEPT ![p][i] = Done]
  /\ UNCHANGED <<opIdQ, opId, opLog>>

Dequeue(p) ==
  /\ Len(opQ[p]) > 0
  /\ Head(opQ[p]) = Done
  /\ opQ'   = [opQ EXCEPT ![p] = Tail(@)]
  /\ opIdQ' = [opIdQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<opId, opLog, opOrder, source, result>>

Respond(p) == \E i \in 1..Len(opQ[p]) : RespondWr(p, i) \/ RespondRd(p, i)

Next ==
  \E p \in Proc :
    \/ \E req \in Request : Issue(p, req)
    \/ Respond(p)
    \/ Dequeue(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Proc : WF_vars(Respond(p))

-----------------------------------------------------------------------------
DataInvariant ==
  /\ opId \in [Proc -> Nat]
  /\ DOMAIN opQ = Proc /\ DOMAIN opIdQ = Proc
  /\ \A p \in Proc :
       /\ Len(opQ[p]) = Len(opIdQ[p])
       /\ Len(opQ[p]) <= QLen
       /\ \A i \in 1..Len(opQ[p]) :
            /\ opQ[p][i] \in Request \cup {Done}
            /\ opIdQ[p][i] \in DOMAIN opLog
            /\ opIdQ[p][i][1] = p
            /\ opIdQ[p][i][2] <= opId[p]
            /\ IsPending(opQ[p][i]) => opLog[opIdQ[p][i]] = opQ[p][i]
            /\ IsPending(opQ[p][i]) /\ opQ[p][i].op = "Rd"
                 => opIdQ[p][i] \notin DOMAIN source
       /\ \A i, j \in 1..Len(opQ[p]) :
            /\ i < j => opIdQ[p][i][2] < opIdQ[p][j][2]
            /\ (i # j /\ IsPending(opQ[p][i]) /\ IsPending(opQ[p][j]))
                 => opQ[p][i].adr # opQ[p][j].adr
  /\ \A id \in DOMAIN opLog : opLog[id] \in Request /\ id[1] \in Proc
  /\ opOrder \subseteq (DOMAIN opLog \X DOMAIN opLog)
  /\ DOMAIN source = DOMAIN result
  /\ DOMAIN source \subseteq DOMAIN opLog
  /\ \A r \in DOMAIN result : result[r] \in Val

Safety ==
  /\ \A r \in DOMAIN source :
       /\ opLog[r].op = "Rd"
       /\ source[r] = InitWr \/ source[r] \in Writes(opLog, opLog[r].adr)
       /\ result[r] = SrcVal(opLog, r, source[r])
  /\ Serializable(opLog, opOrder, source)

Liveness == \A p \in Proc : []((\E i \in 1..Len(opQ[p]) : IsPending(opQ[p][i]))
                                 ~> (\A i \in 1..Len(opQ[p]) : ~IsPending(opQ[p][i])))
=============================================================================