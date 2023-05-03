---- MODULE FIFO ----
\* NOTE: this is uncheckable by TLC. It cannot handle
\* existential quantification over state variables...
\* Apparently Specifying Systems was written without 
\* the tools to check it...
EXTENDS TLC
CONSTANT Message
VARIABLES in, out

Inner(q) == INSTANCE InnerFIFO

Spec == \EE q : Inner(q)!Init /\ Inner(q)!Spec

====