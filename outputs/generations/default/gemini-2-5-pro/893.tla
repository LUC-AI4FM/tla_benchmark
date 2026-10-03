---- MODULE OnePlaceChannel ----
EXTENDS Integers

CONSTANT Data

VARIABLES chan

(*
--algorithm OnePlaceChannel
variable chan = [val |-> d, rdy |-> 0, ack |-> 0]
    for d \in Data;

begin
    while TRUE do
        either
            with d \in Data do
                await chan.rdy = chan.ack;
                chan.val := d;
                chan.rdy := 1 - chan.rdy;
            end with;
        or
            await chan.rdy # chan.ack;
            chan.ack := 1 - chan.ack;
        end either;
    end while;
end algorithm;
*)

TypeOK ==
    /\ chan.val \in Data
    /\ chan.rdy \in {0, 1}
    /\ chan.ack \in {0, 1}

Init ==
    \E d \in Data:
        chan = [val |-> d, rdy |-> 0, ack |-> 0]

Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Receive ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next ==
    \/ \E d \in Data: Send(d)
    \/ Receive

Spec == Init /\ [][Next]_chan

THEOREM Spec => []TypeOK

================================