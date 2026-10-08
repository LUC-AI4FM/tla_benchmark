----------------------------- MODULE LockFreeDeque -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  P,            \* Set of process identifiers
  Addr,         \* Finite set of node addresses
  S,            \* Distinguished sentinel address in Addr
  Values,       \* Set of storable values
  Tokens,       \* Set of unique push-instance identifiers
  NullToken,    \* Distinguished token not in Tokens
  NoneVal       \* Distinguished value not in Values

ASSUME
  /\ S \in Addr
  /\ NullToken \notin Tokens
  /\ NoneVal \notin Values

\* State variables (concrete deque and verification harness)
VARIABLES
  next,         \* [Addr -> Addr] next pointers (circular with sentinel)
  prev,         \* [Addr -> Addr] prev pointers (circular with sentinel)
  val,          \* [Addr -> Values \cup {NoneVal}] stored value in node
  nid,          \* [Addr -> Tokens \cup {NullToken}] token bound to node
  free,         \* SUBSET Addr, pool of free nodes (never includes S)
  absTok,       \* Sequence of Tokens representing the abstract deque contents, left..right
  tval,         \* [Tokens -> Values \cup {NoneVal}] value associated to a token
  lastRes,      \* [P -> [op: Ops, status: Status, what: Values \cup {NoneVal}, token: Tokens \cup {NullToken}]]
  AllPushed,    \* Set of tokens used by successful pushes (never reused)
  Returned      \* Set of tokens returned by successful pops

Vars == << next, prev, val, nid, free, absTok, tval, lastRes, AllPushed, Returned >>

Ops == {"PushL","PushR","PopL","PopR","None"}
Status == {"okay","empty","full"}

IsEmpty == /\ next[S] = S /\ prev[S] = S

Elems(s) == { s[i] : i \in DOMAIN s }

TokensOnNodes ==
  { nid[a] : a \in Addr \ {S} : a \notin free /\ nid[a] \in Tokens }

TypeInv ==
  /\ next \in [Addr -> Addr]
  /\ prev \in [Addr -> Addr]
  /\ val \in [Addr -> Values \cup {NoneVal}]
  /\ nid \in [Addr -> Tokens \cup {NullToken}]
  /\ free \subseteq Addr
  /\ S \notin free
  /\ absTok \in Seq(Tokens)
  /\ tval \in [Tokens -> Values \cup {NoneVal}]
  /\ lastRes \in [P -> [op: Ops, status: Status, what: Values \cup {NoneVal}, token: Tokens \cup {NullToken}]]
  /\ AllPushed \subseteq Tokens
  /\ Returned \subseteq Tokens

\* Structural/semantic correspondence between concrete and abstract state
EndsMatchInv ==
  /\ (Len(absTok) = 0) => (next[S] = S /\ prev[S] = S)
  /\ (Len(absTok) > 0)
        => /\ next[S] # S /\ prev[S] # S
           /\ nid[next[S]] = absTok[1]
           /\ nid[prev[S]] = absTok[Len(absTok)]

FreeNodesWellFormed ==
  \A a \in free:
    /\ a # S
    /\ next[a] = a
    /\ prev[a] = a
    /\ val[a] = NoneVal
    /\ nid[a] = NullToken

NoLostInv ==
  /\ AllPushed = Returned \cup Elems(absTok)
  /\ Returned \cap Elems(absTok) = {}
  /\ Elems(absTok) = TokensOnNodes

SafetyInv == TypeInv /\ EndsMatchInv /\ FreeNodesWellFormed /\ NoLostInv

Init ==
  /\ next = [a \in Addr |-> IF a = S THEN S ELSE a]
  /\ prev = [a \in Addr |-> IF a = S THEN S ELSE a]
  /\ val  = [a \in Addr |-> NoneVal]
  /\ nid  = [a \in Addr |-> NullToken]
  /\ free = Addr \ {S}
  /\ absTok = << >>
  /\ tval = [t \in Tokens |-> NoneVal]
  /\ lastRes = [p \in P |-> [op |-> "None", status |-> "empty", what |-> NoneVal, token |-> NullToken]]
  /\ AllPushed = {}
  /\ Returned = {}

\* Double-Compare-And-Swap is modeled by the guarded simultaneous updates of two memory cells.
\* Each push/pop action checks two locations (the DCAS "expected" pair) and, if both match,
\* performs the corresponding pair of updates atomically, along with the associated bookkeeping.

PushLeftSucc(p) ==
  /\ p \in P
  /\ free \ {S} # {}
  /\ \E a \in free, x \in Values, t \in (Tokens \ AllPushed):
        IF IsEmpty
        THEN
          /\ next[S] = S /\ prev[S] = S
          /\ next' = [next EXCEPT ![S] = a, ![a] = S]
          /\ prev' = [prev EXCEPT ![S] = a, ![a] = S]
        ELSE
          LET f == next[S] IN
            /\ next[S] = f /\ prev[f] = S
            /\ next' = [next EXCEPT ![S] = a, ![a] = f]
            /\ prev' = [prev EXCEPT ![f] = a, ![a] = S]
        /\ val' = [val EXCEPT ![a] = x]
        /\ nid' = [nid EXCEPT ![a] = t]
        /\ free' = free \ {a}
        /\ absTok' = << t >> \o absTok
        /\ tval' = [tval EXCEPT ![t] = x]
        /\ lastRes' = [lastRes EXCEPT ![p] = [op |-> "PushL", status |-> "okay", what |-> x, token |-> t]]
        /\ AllPushed' = AllPushed \cup {t}
        /\ Returned' = Returned

  \/ \* stuttering branch here is intentionally omitted; this action only models success

PushLeftFull(p) ==
  /\ p \in P
  /\ free = {}
  /\ UNCHANGED << next, prev, val, nid, free, absTok, tval, AllPushed, Returned >>
  /\ lastRes' = [lastRes EXCEPT ![p] = [op |-> "PushL", status |-> "full", what |-> NoneVal, token |-> NullToken]]

PushRightSucc(p) ==
  /\ p \in P
  /\ free \ {S} # {}
  /\ \E a \in free, x \in Values, t \in (Tokens \ AllPushed):
        IF IsEmpty
        THEN
          /\ next[S] = S /\ prev[S] = S
          /\ next' = [next EXCEPT ![S] = a, ![a] = S]
          /\ prev' = [prev EXCEPT ![S] = a, ![a] = S]
        ELSE
          LET l == prev[S] IN
            /\ prev[S] = l /\ next[l] = S
            /\ prev' = [prev EXCEPT ![S] = a, ![a] = l]
            /\ next' = [next EXCEPT ![l] = a, ![a] = S]
        /\ val' = [val EXCEPT ![a] = x]
        /\ nid' = [nid EXCEPT ![a] = t]
        /\ free' = free \ {a}
        /\ absTok' = Append(absTok, t)
        /\ tval' = [tval EXCEPT ![t] = x]
        /\ lastRes' = [lastRes EXCEPT ![p] = [op |-> "PushR", status |-> "okay", what |-> x, token |-> t]]
        /\ AllPushed' = AllPushed \cup {t}
        /\ Returned' = Returned

PushRightFull(p) ==
  /\ p \in P
  /\ free = {}
  /\ UNCHANGED << next, prev, val, nid, free, absTok, tval, AllPushed, Returned >>
  /\ lastRes' = [lastRes EXCEPT ![p] = [op |-> "PushR", status |-> "full", what |-> NoneVal, token |-> NullToken]]

PopLeftOk(p) ==
  /\ p \in P
  /\ ~IsEmpty
  LET f == next[S] IN
  LET s == next[f] IN
  LET t == nid[f] IN
    /\ absTok # << >>
    /\ t = absTok[1]
    /\ IF s = S
       THEN
         /\ next[S] = f /\ prev[S] = f
         /\ next' = [next EXCEPT ![S] = S, ![f] = f]
         /\ prev' = [prev EXCEPT ![S] = S, ![f] = f]
       ELSE
         /\ next[S] = f /\ prev[s] = f
         /\ next' = [next EXCEPT ![S] = s, ![f] = f]
         /\ prev' = [prev EXCEPT ![s] = S, ![f] = f]
    /\ free' = free \cup {f}
    /\ val' = [val EXCEPT ![f] = NoneVal]
    /\ nid' = [nid EXCEPT ![f] = NullToken]
    /\ absTok' = Tail(absTok)
    /\ tval' = tval
    /\ lastRes' = [lastRes EXCEPT ![p] = [op |-> "PopL", status |-> "okay", what |-> tval[t], token |-> t]]
    /\ AllPushed' = AllPushed
    /\ Returned' = Returned \cup {t}

PopLeftEmpty(p) ==
  /\ p \in P
  /\ IsEmpty
  /\ UNCHANGED << next, prev, val, nid, free, absTok, tval, AllPushed, Returned >>
  /\ lastRes' = [lastRes EXCEPT ![p] = [op |-> "PopL", status |-> "empty", what |-> NoneVal, token |-> NullToken]]

PopRightOk(p) ==
  /\ p \in P
  /\ ~IsEmpty
  LET l == prev[S] IN
  LET u == prev[l] IN
  LET t == nid[l] IN
    /\ absTok # << >>
    /\ t = absTok[Len(absTok)]
    /\ IF u = S
       THEN
         /\ prev[S] = l /\ next[S] = l
         /\ prev' = [prev EXCEPT ![S] = S, ![l] = l]
         /\ next' = [next EXCEPT ![S] = S, ![l] = l]
       ELSE
         /\ prev[S] = l /\ next[u] = l
         /\ prev' = [prev EXCEPT ![S] = u, ![l] = l]
         /\ next' = [next EXCEPT ![u] = S, ![l] = l]
    /\ free' = free \cup {l}
    /\ val' = [val EXCEPT ![l] = NoneVal]
    /\ nid' = [nid EXCEPT ![l] = NullToken]
    /\ absTok' = SubSeq(absTok, 1, Len(absTok)-1)
    /\ tval' = tval
    /\ lastRes' = [lastRes EXCEPT ![p] = [op |-> "PopR", status |-> "okay", what |-> tval[t], token |-> t]]
    /\ AllPushed' = AllPushed
    /\ Returned' = Returned \cup {t}

PopRightEmpty(p) ==
  /\ p \in P
  /\ IsEmpty
  /\ UNCHANGED << next, prev, val, nid, free, absTok, tval, AllPushed, Returned >>
  /\ lastRes' = [lastRes EXCEPT ![p] = [op |-> "PopR", status |-> "empty", what |-> NoneVal, token |-> NullToken]]

Step(p) ==
   PushLeftSucc(p)
\/ PushLeftFull(p)
\/ PushRightSucc(p)
\/ PushRightFull(p)
\/ PopLeftOk(p)
\/ PopLeftEmpty(p)
\/ PopRightOk(p)
\/ PopRightEmpty(p)

Next ==
  \E p \in P : Step(p)

Spec ==
  Init /\ [][Next]_Vars /\ \A p \in P : WF_Vars(Step(p))

\* Safety invariants to be checked in the model:
\*  - SafetyInv includes:
\*     - Type well-formedness
\*     - Ends of concrete deque match abstract order
\*     - Free nodes are isolated and carry no data
\*     - No lost or duplicated tokens: AllPushed = Returned ⊎ Elems(absTok)
===============================================================================