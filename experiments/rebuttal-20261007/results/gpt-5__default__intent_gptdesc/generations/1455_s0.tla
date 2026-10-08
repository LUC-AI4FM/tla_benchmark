--------------------------- MODULE SubsetRelationReasoning ---------------------------

EXTENDS Integers, FiniteSets

CONSTANTS RN, ELEMS, FIN_INT_SETS, FIN_NAT_SETS

ASSUME
  /\ RN \subseteq Nat
  /\ ELEMS \subseteq Int
  /\ FIN_INT_SETS \subseteq SUBSET Int
  /\ FIN_NAT_SETS \subseteq FIN_INT_SETS
  /\ FIN_NAT_SETS \subseteq SUBSET Nat
  /\ \A S \in FIN_INT_SETS : IsFiniteSet(S)
  /\ \A S \in FIN_NAT_SETS : IsFiniteSet(S)

Rng(n) == 1..n

Ranges ==
  { S \in SUBSET Int : \E n \in RN : S = Rng(n) }

SingletonSets ==
  { S \in SUBSET Int : \E e \in ELEMS : S = {e} }

BaseSets == Ranges \cup FIN_INT_SETS \cup SingletonSets \cup {Nat, Int, {}}

BasePairs == BaseSets \X BaseSets

IsSubSem(p) ==
  /\ p \in BasePairs
  /\ LET A == p[1] IN LET B == p[2] IN A \subseteq B

IsNotSubSem(p) ==
  /\ p \in BasePairs
  /\ LET A == p[1] IN LET B == p[2] IN ~(A \subseteq B)

MandatedEmptySub ==
  { p \in BasePairs : p[1] = {} }

MandatedRangeSub ==
  { p \in BasePairs :
      \E n \in RN, m \in RN :
        /\ p = << Rng(n), Rng(m) >>
        /\ n <= m }

MandatedFinIntToInt ==
  { p \in BasePairs : /\ p[1] \in FIN_INT_SETS /\ p[2] = Int }

MandatedFinNatToNat ==
  { p \in BasePairs : /\ p[1] \in FIN_NAT_SETS /\ p[2] = Nat }

MandatedSub ==
  MandatedEmptySub \cup MandatedRangeSub \cup MandatedFinIntToInt \cup MandatedFinNatToNat

MandatedRangeNotSub ==
  { p \in BasePairs :
      \E n \in RN, m \in RN :
        /\ p = << Rng(n), Rng(m) >>
        /\ n > m }

MandatedSingletonNotSubEmpty ==
  { p \in BasePairs : /\ p[1] \in SingletonSets /\ p[2] = {} }

MandatedNotSub ==
  MandatedRangeNotSub \cup MandatedSingletonNotSubEmpty

VARIABLES SubRel, NotSubRel, consistent

vars == << SubRel, NotSubRel, consistent >>

Init ==
  /\ SubRel = MandatedSub
  /\ NotSubRel = MandatedNotSub
  /\ consistent = TRUE

CanAddSub ==
  { p \in BasePairs : /\ IsSubSem(p) /\ ~(p \in NotSubRel) }

CanAddNotSub ==
  { p \in BasePairs : /\ IsNotSubSem(p) /\ ~(p \in SubRel) }

Next ==
  \E addS \in SUBSET CanAddSub, addN \in SUBSET CanAddNotSub :
    /\ SubRel' = SubRel \cup addS
    /\ NotSubRel' = NotSubRel \cup addN
    /\ consistent' = TRUE

Spec == Init /\ [][Next]_vars

(*
  Safety invariants capturing correctness and preservation
*)
TypeOK ==
  /\ SubRel \subseteq BasePairs
  /\ NotSubRel \subseteq BasePairs
  /\ consistent \in BOOLEAN

TruthOK ==
  /\ \A p \in SubRel : IsSubSem(p)
  /\ \A p \in NotSubRel : IsNotSubSem(p)

DisjointOK ==
  SubRel \cap NotSubRel = {}

MandatesPreserved ==
  /\ MandatedSub \subseteq SubRel
  /\ MandatedNotSub \subseteq NotSubRel

ConsistencyFlagAlwaysTrue ==
  consistent = TRUE

SafetyInv ==
  TypeOK /\ TruthOK /\ DisjointOK /\ MandatesPreserved /\ ConsistencyFlagAlwaysTrue

=============================================================================