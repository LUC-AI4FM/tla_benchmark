------------------------------- MODULE ConcurrentQueue -------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N, Clients, Values

VARIABLES queue, clientResults

Init == /\ queue = << >>
        /\ clientResults \in [Clients -> {<<>>, "full", "empty"}]

Next ==
    \/ \E c \in Clients : 
        (clientResults[c] = << >>) /\
        (\E v \in Values :
            \/ /\ queue' = Append(queue, v)
               /\ clientResults' = [clientResults EXCEPT ![c] = <<v>>]
            \/ /\ queue' = Prepend(queue, v)
               /\ clientResults' = [clientResults EXCEPT ![c] = <<v>>]
        )
    \/ \E c \in Clients : 
        (clientResults[c] = << >>) /\
        (\E i \in 1..Len(queue) :
            queue' = Except(queue, i)
            /\ clientResults' = [clientResults EXCEPT ![c] = <<queue[i]>>]
        )
    \/ \E c \in Clients : 
        (clientResults[c] \in {<<>>, "full", "empty"}) /\
        clientResults' = [clientResults EXCEPT ![c] = << >>]

Spec ==
    /\ Init
    /\ [][Next]_<<queue, clientResults>>
    /\ WFClientFairness

WFClientFairness == 
    /\ \A c \in Clients : WFFair({s \in SUCCESSION(Next) : queue' # queue /\ clientResults'[c] = "full" \/ queue' # queue /\ clientResults'[c] = "empty"})
    /\ \A c \in Clients : WFFair({s \in SUCCESSION(Next) : queue' # queue /\ clientResults'[c] \in Values})

QueueCapacityBound == Len(queue) <= N

NoSpuriousValues ==
    \A v \in Values :
        ~(\E s \in SUCCESSION(Next) : clientResults'[s] = <<v>> /\ ~(\E i \in 1..Len(queue) : queue[i] = v))

EnqueueSuccessPlacesValue ==
    \A s, s' \in SUCCESSION(Next), c \in Clients :
        (clientResults[s] = << >> /\ clientResults'[s'] = <<v>>)
        -> (\E i \in 1..Len(queue) : queue[i] = v)

Spec == Spec /\ QueueCapacityBound /\ NoSpuriousValues /\ EnqueueSuccessPlacesValue

=============================================================================