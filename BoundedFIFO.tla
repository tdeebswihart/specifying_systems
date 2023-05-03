---- MODULE BoundedFIFO ----
EXTENDS InnerFIFO

CONSTANT qLen

qConstraint == Len(q) \leq qLen

====