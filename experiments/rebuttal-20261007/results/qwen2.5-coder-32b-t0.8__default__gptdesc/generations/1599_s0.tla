------------------------------- MODULE FastMutualExclusion -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES x, y, b

(*--algorithm fast_mutual_exclusion
variables 
  x = 0,
  y = 0,
  b = <<FALSE \:> N>>;

process process \in 1..N
begin
    while TRUE do
        with (x' = self) /\ (y' = 0);
            await (\A i \in 1..N : \neg b[i] \/ i = x');
        with (b[x'] = TRUE);
            await (y' = 0 \/ y' = x');
        with (y' = x');
            await (\A i \in 1..N : \neg (i \neq x' /\ b[i] /\ i = y'));
        critical_section: skip;
        with (b[x'] = FALSE);
    end while
end process
*)

Init == \/ N = 0
        \/ /\ x = 0 
           /\ y = 0
           /\ b = <<FALSE \:> N>>

Next ==
  \E p \in 1..N : 
    \/ /\ x' = p
       /\ y' = 0
       /\ \A i \in 1..N : \neg b[i] \/ i = p
       /\ UNCHANGED <<b>>
    \/ /\ b[x] = TRUE
       /\ y' = 0 \/ y' = x
       /\ UNCHANGED <<x, b>>
    \/ /\ y' = x
       /\ \A i \in 1..N : \neg (i \neq x /\ b[i] /\ i = y)
       /\ UNCHANGED <<x, b>>
    \/ /\ b[x] = FALSE
       /\ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_<<x,y,b>> /\ WF_x(Next) /\ WF_y(Next) /\ SF_b(Next)

MutualExclusion ==
  \A p, q \in 1..N : 
    \/ p = q
    \/ \neg (b[p] /\ b[q])

WF_x == [](x' = x \/ x' \in 1..N)
WF_y == [](y' = y \/ y' \in 0..N)
SF_b ==
  \A i \in 1..N :
    <>(\E j \in 1..N : b[j]) => <>[b[i] = TRUE]

Liveness ==
  \A p \in 1..N : <><critical_section>_p

ConditionalLiveness ==
  \A p \in 1..N : 
    (\E q \in 1..N : p \neq q /\ b[q]) => <><critical_section>_p

FairSpec == Spec /\ Liveness /\ ConditionalLiveness
=============================================================================