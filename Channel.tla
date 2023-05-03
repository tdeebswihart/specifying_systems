---- MODULE Channel ----
EXTENDS TLC, Naturals
CONSTANT Data
VARIABLES chan

TypeInvariant == chan \in [val: Data, rdy: {0, 1}, ack: {0, 1}]
----
Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

\* May only send once previous send it acknowledged
Send(d) == 
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

\* May only send when there is data to read, i.e. rdy != ack
Recv == /\ chan.rdy # chan.ack
        /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == (\E d \in Data : Send(d)) \/ Recv

Spec == Init /\ [][Next]_chan
----
THEOREM Spec => []TypeInvariant
====