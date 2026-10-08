------------------------------- MODULE SpanningTreeRandom -------------------------------

CONSTANTS Nodes, Root, MaxCardinality

ASSUME Root \in Nodes
ASSUME MaxCardinality \in Nat /\ Cardinality(Nodes) <= MaxCardinality

VARIABLES mom, dist

(*--algorithm spanning-tree-random
variables 
    mom = [n \in Nodes |-> n],
    dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality];

fair process (ALL_NODES \in Nodes)
vars n, m, newDist;
begin
    while TRUE do
        with n \in Nodes \ {Root} do
            with m \in {nn \in Nodes : nn # n /\ <<n, nn>> \in Edges} do
                if dist[m] < dist[n] - 1 then
                    newDist := RandomElement({d \in (dist[m]+1)..(dist[n]-1)});
                    mom[n] := m;
                    dist[n] := newDist;
                end if;
            end with;
        end with;
    end while;
end process;

end algorithm;)

Edges == [n \in Nodes |-> RandomElement(SUBSET {nn \in Nodes : nn # n})]

TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> 0..MaxCardinality]
    /\ (forall n \in Nodes: mom[n] \in Nodes)
    /\ (forall n \in Nodes: dist[n] \in 0..MaxCardinality)

Safety ==
    LET reachable == {n \in Nodes : dist[n] < MaxCardinality}
        in
            /\ (forall n \in reachable: dist[mom[n]] + 1 = dist[n])
            /\ (forall n \notin reachable: dist[n] = MaxCardinality)
            /\ (forall n \notin reachable, m \in {nn \in Nodes : nn # n}: <<n, m>> \in Edges => dist[m] = MaxCardinality)

PostCondition ==
    LET reachable == {n \in Nodes : dist[n] < MaxCardinality}
        in
            /\ (forall n \in reachable: dist[mom[n]] + 1 = dist[n])
            /\ (forall n \notin reachable: dist[n] = MaxCardinality)
            /\ (forall n \notin reachable, m \in {nn \in Nodes : nn # n}: <<n, m>> \in Edges => dist[m] = MaxCardinality)

Spec ==
    /\ TypeOK
    /\ WF_next(<<mom, dist>>)
    /\ []TypeOK
    /\ [](dist[Root] = 0)
    /\ <>(PostCondition)

Liveness == <>(PostCondition)

=============================================================================