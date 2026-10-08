------------------------------- MODULE HuangAlgorithm -------------------------------

CONSTANTS Procs, Leader

VARIABLES weights, queues, active

ASSUME Cardinality(Procs) \geq 2 /\ Leader \in Procs

(*--algorithm HuangAlgorithm
variables 
    weights = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0],
    queues  = [p \in Procs |-> <<>>],
    active  = {Leader};

fair process (p \in Procs) \in Procs
begin
    while TRUE do
        if p \notin active then
            await queues[p] # <<>>;
            let m = Head(queues[p]) in
                queues' = [queues EXCEPT ![p] = Tail(queues[p])],
                weights' = [weights EXCEPT ![p] = weights[p] + m, ![Sender(m)] = weights[Sender(m)] - m],
                active' = active \cup {p}
            end let;
        else
            if p = Leader then
                either
                    await queues[p] # <<>>;
                    let m = Head(queues[p]) in
                        queues' = [queues EXCEPT ![p] = Tail(queues[p])],
                        weights' = [weights EXCEPT ![p] = weights[p] + m, ![Sender(m)] = weights[Sender(m)] - m]
                    end let;
                or
                    await active # {Leader};
                    let q \in (active \ {Leader}) in
                        queues' = [queues EXCEPT ![Leader] = Append(queues[Leader], weights[q])],
                        weights' = [weights EXCEPT ![q] = 0],
                        active' = active \ {q}
                end either;
            else
                let q \in (Procs \ {p}) in
                    queues' = [queues EXCEPT ![q] = Append(queues[q], weights[p]/2)],
                    weights' = [weights EXCEPT ![p] = weights[p]/2],
                    active' = IF weights[p]/2 = 0 THEN active \ {p} ELSE active;
                end let;
            end if;
        end if;
    od;
end process;

fairness assume
    WF_{<<queues[p] # <<>> >>}(p \in Procs)
    /\ WF_{<<active # {Leader} >>}(p = Leader);

TypeOK == 
    /\ \A p \in Procs: weights[p] \in 0..1
    /\ \A p \in Procs: queues[p] \in Seq(0..1)
    /\ active \subseteq Procs

WeightConservation ==
    Sum(weights) + Sum(\A p \in Procs: Sum(queues[p])) = 1

StateConstraint ==
    \A p \in Procs: weights[p] \in {x \in 0..1 : \E n \in Nat: x = m/2^n}

Spec == 
    /\ TypeOK
    /\ WeightConservation
    /\ StateConstraint
    /\ Init /\ [][Next]_<<vars>>

Safe ==
    [](\/ active # {Leader} \/ queues[Leader] # <<>> => \/ active # {Leader} \/ queues[Leader] # <<>>)

Live ==
    <>(active = {Leader} /\ queues[Leader] = <<>>)

THEOREM Spec => []<>(active = {Leader} /\ queues[Leader] = <<>>)
THEOREM Spec => [](active = {Leader} /\ queues[Leader] = <<>> => stable(active = {Leader} /\ queues[Leader] = <<>>))

=============================================================================