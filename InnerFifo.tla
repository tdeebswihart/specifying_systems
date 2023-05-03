---- MODULE InnerFifo ----
\* InnerFifo describes the inside of a FIFO queue mediated by the 
\* protocol described in Channel.tla
EXTENDS TLC, Naturals, Sequences

CONSTANT Message
VARIABLES in, out, q

InChan == INSTANCE Channel WITH Data <- Message, chan <- in
OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

TypeInvariant == /\ InChan!TypeInvariant
                 /\ OutChan!TypeInvariant
                 /\ q \in Seq(Message)

Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = <<>>

\* Sender sends along `in`
SSend(msg) == /\ InChan!Send(msg)
              /\ UNCHANGED <<out, q>>

\* Messages are buffered from `in` into `q`
BufRcv == /\ InChan!Recv 
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out

\* The recipient is able to accept another message
BufSend == /\ q # <<>>
           /\ OutChan!Send(Head(q))
           /\ q' = Tail(q)
           /\ UNCHANGED in

\* Recipient receives the message
RRecv == /\ OutChan!Recv
         /\ UNCHANGED <<in, q>>

Next == \/ \E msg \in Message : SSend(msg)
        \/ BufRcv
        \/ BufSend
        \/ RRecv

Spec == Init /\ [][Next]_<<in, out, q>>

----
THEOREM Spec => []TypeInvariant
====
