------------------------------- MODULE graph -------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Nodes, Edge(_,_)
RECURSIVE Path(_,_,_)
Path(x, y, n) == IF n = 0 THEN x = y
                ELSE \E z \in Nodes : Path(x, z, n-1) /\ Edge(z, y)

Connected(x, y) == \E n \in 0..Cardinality(Nodes) : Path(x, y, n)

AllConnected(S) == \A x, y \in S : Connected(x, y) /\ Connected(y, x)

SCC(S) == /\ AllConnected(S)
            /\ \A T \in SUBSET Nodes :
                S \subseteq T /\ AllConnected(T) => S = T
                



=============================================================================
\* Modification History
\* Last modified Wed Jan 22 19:38:23 CET 2020 by matth_000
\* Created Tue Jan 21 20:05:30 CET 2020 by matth_000
