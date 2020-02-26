------------------------------- MODULE Tarjan -------------------------------
EXTENDS FiniteSets, Sequences, Integers, SCC

(***************************************************************************)
(* The algorithm in pseudo-code (from Wikipedia):                          *)
(*                                                                         *)
(* algorithm tarjan is                                                     *)
(*     input: graph G = (V, E)                                             *)
(*     output: set of strongly connected components (sets of vertices)     *)
(*                                                                         *)
(*     index := 0                                                          *)
(*     S := empty stack                                                    *)
(*     for each v in V do                                                  *)
(*         if v.index is undefined then                                    *)
(*             strongconnect(v)                                            *)
(*         end if                                                          *)
(*     end for                                                             *)
(*                                                                         *)
(*     function strongconnect(v)                                           *)
(*         // Set the depth index for v to the smallest unused index       *)
(*         v.index := index                                                *)
(*         v.lowlink := index                                              *)
(*         index := index + 1                                              *)
(*         S.push(v)                                                       *)
(*         v.onStack := true                                               *)
(*                                                                         *)
(*         // Consider successors of v                                     *)
(*         for each (v, w) in E do                                         *)
(*             if w.index is undefined then                                *)
(*                 // Successor w has not yet been visited; recurse on it  *)
(*                 strongconnect(w)                                        *)
(*                 v.lowlink := min(v.lowlink, w.lowlink)                  *)
(*             else if w.onStack then                                      *)
(*                 // Successor w is in stack S and hence in the current SCC *)
(*                 // If w is not on stack, then (v, w) is a cross-edge in the DFS tree and must be ignored *)
(*                 // Note: The next line may look odd - but is correct.   *)
(*                 // It says w.index not w.lowlink; that is deliberate and from the original paper *)
(*                 v.lowlink := min(v.lowlink, w.index)                    *)
(*             end if                                                      *)
(*         end for                                                         *)
(*                                                                         *)
(*         // If v is a root node, pop the stack and generate an SCC       *)
(*         if v.lowlink = v.index then                                     *)
(*             start a new strongly connected component                    *)
(*             repeat                                                      *)
(*                 w := S.pop()                                            *)
(*                 w.onStack := false                                      *)
(*                 add w to current strongly connected component           *)
(*             while w ≠ v                                                 *)
(*             output the current strongly connected component             *)
(*         end if                                                          *)
(*     end function                                                        *)
(*                                                                         *)
(* We rewrite this algorithm in PlusCal, an algorithm language that has a  *)
(* translator for generating a TLA+ specification.                         *)
(***************************************************************************)

(*--algorithm Tarjan {
  variables 
    index = 0, 
    t_stack = << >>, 
    num = [n \in Nodes |-> -1], 
    lowlink = [n \in Nodes |-> -1], 
    onStack = [n \in Nodes |-> FALSE], 
    sccs = {},
    toVisit = Nodes;

  procedure visit(v) 
    variable succs, w; 
  {
start_visit:
    num[v] := index;
    lowlink[v] := index;
    index := index+1;
    t_stack := <<v>> \o t_stack;
    onStack[v] := TRUE;
    succs := Succs[v];

explore_succ:    
    while (succs # {}) {
      with (s \in succs) { w := s; succs := succs \ {s} };
      if (num[w] = -1) {
visit_recurse:
        call visit(w);
continue_visit:
        if (lowlink[w] < lowlink[v]) { lowlink[v] := lowlink[w] }
      } else if (onStack[w]) {
        if (num[w] < lowlink[v]) { lowlink[v] := num[w] }
      }
    };
check_root:
    if (lowlink[v] = num[v]) {
      \* new SCC found: pop all nodes up to v from the (Tarjan) stack
      with (k = CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v) {
        sccs := sccs \cup {{t_stack[i] : i \in 1 .. k}};
        onStack := [n \in Nodes |-> IF \E i \in 1 .. k : n = t_stack[i] THEN FALSE
                                    ELSE onStack[n]];
        t_stack := SubSeq(t_stack, k+1, Len(t_stack))
      }
    };
    return;
  }
  
  { \* body of main algorithm
main:
    while (toVisit # {}) {
      with (n \in toVisit) {
        toVisit := toVisit \ {n};
        if (num[n] = -1) { call visit(n) }
      }
    }
  }
}
*)
\* BEGIN TRANSLATION PCal-1c130795fb3a667de4cc07aa7095f6e0
CONSTANT defaultInitValue
VARIABLES index, t_stack, num, lowlink, onStack, sccs, toVisit, pc, stack, v, 
          succs, w

vars == << index, t_stack, num, lowlink, onStack, sccs, toVisit, pc, stack, v, 
           succs, w >>

Init == (* Global variables *)
        /\ index = 0
        /\ t_stack = << >>
        /\ num = [n \in Nodes |-> -1]
        /\ lowlink = [n \in Nodes |-> -1]
        /\ onStack = [n \in Nodes |-> FALSE]
        /\ sccs = {}
        /\ toVisit = Nodes
        (* Procedure visit *)
        /\ v = defaultInitValue
        /\ succs = defaultInitValue
        /\ w = defaultInitValue
        /\ stack = << >>
        /\ pc = "main"

start_visit == /\ pc = "start_visit"
               /\ num' = [num EXCEPT ![v] = index]
               /\ lowlink' = [lowlink EXCEPT ![v] = index]
               /\ index' = index+1
               /\ t_stack' = <<v>> \o t_stack
               /\ onStack' = [onStack EXCEPT ![v] = TRUE]
               /\ succs' = Succs[v]
               /\ pc' = "explore_succ"
               /\ UNCHANGED << sccs, toVisit, stack, v, w >>

explore_succ == /\ pc = "explore_succ"
                /\ IF succs # {}
                      THEN /\ \E s \in succs:
                                /\ w' = s
                                /\ succs' = succs \ {s}
                           /\ IF num[w'] = -1
                                 THEN /\ pc' = "visit_recurse"
                                      /\ UNCHANGED lowlink
                                 ELSE /\ IF onStack[w']
                                            THEN /\ IF num[w'] < lowlink[v]
                                                       THEN /\ lowlink' = [lowlink EXCEPT ![v] = num[w']]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED lowlink
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED lowlink
                                      /\ pc' = "explore_succ"
                      ELSE /\ pc' = "check_root"
                           /\ UNCHANGED << lowlink, succs, w >>
                /\ UNCHANGED << index, t_stack, num, onStack, sccs, toVisit, 
                                stack, v >>

visit_recurse == /\ pc = "visit_recurse"
                 /\ /\ stack' = << [ procedure |->  "visit",
                                     pc        |->  "continue_visit",
                                     succs     |->  succs,
                                     w         |->  w,
                                     v         |->  v ] >>
                                 \o stack
                    /\ v' = w
                 /\ succs' = defaultInitValue
                 /\ w' = defaultInitValue
                 /\ pc' = "start_visit"
                 /\ UNCHANGED << index, t_stack, num, lowlink, onStack, sccs, 
                                 toVisit >>

continue_visit == /\ pc = "continue_visit"
                  /\ IF lowlink[w] < lowlink[v]
                        THEN /\ lowlink' = [lowlink EXCEPT ![v] = lowlink[w]]
                        ELSE /\ TRUE
                             /\ UNCHANGED lowlink
                  /\ pc' = "explore_succ"
                  /\ UNCHANGED << index, t_stack, num, onStack, sccs, toVisit, 
                                  stack, v, succs, w >>

check_root == /\ pc = "check_root"
              /\ IF lowlink[v] = num[v]
                    THEN /\ LET k == CHOOSE k \in 1 .. Len(t_stack) : t_stack[k] = v IN
                              /\ sccs' = (sccs \cup {{t_stack[i] : i \in 1 .. k}})
                              /\ onStack' = [n \in Nodes |-> IF \E i \in 1 .. k : n = t_stack[i] THEN FALSE
                                                             ELSE onStack[n]]
                              /\ t_stack' = SubSeq(t_stack, k+1, Len(t_stack))
                    ELSE /\ TRUE
                         /\ UNCHANGED << t_stack, onStack, sccs >>
              /\ pc' = Head(stack).pc
              /\ succs' = Head(stack).succs
              /\ w' = Head(stack).w
              /\ v' = Head(stack).v
              /\ stack' = Tail(stack)
              /\ UNCHANGED << index, num, lowlink, toVisit >>

visit == start_visit \/ explore_succ \/ visit_recurse \/ continue_visit
            \/ check_root

main == /\ pc = "main"
        /\ IF toVisit # {}
              THEN /\ \E n \in toVisit:
                        /\ toVisit' = toVisit \ {n}
                        /\ IF num[n] = -1
                              THEN /\ /\ stack' = << [ procedure |->  "visit",
                                                       pc        |->  "main",
                                                       succs     |->  succs,
                                                       w         |->  w,
                                                       v         |->  v ] >>
                                                   \o stack
                                      /\ v' = n
                                   /\ succs' = defaultInitValue
                                   /\ w' = defaultInitValue
                                   /\ pc' = "start_visit"
                              ELSE /\ pc' = "main"
                                   /\ UNCHANGED << stack, v, succs, w >>
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << toVisit, stack, v, succs, w >>
        /\ UNCHANGED << index, t_stack, num, lowlink, onStack, sccs >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == visit \/ main
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION TLA-4824c568ebcdda4689e9f5c995f8b0e3



=============================================================================
\* Modification History
\* Last modified Thu Feb 20 18:37:24 CET 2020 by merz
\* Created Thu Feb 20 14:43:38 CET 2020 by merz
