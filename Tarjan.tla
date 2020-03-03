------------------------------- MODULE Tarjan -------------------------------
EXTENDS FiniteSets, Sequences, Integers, SCC, TLAPS

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
    variable succs = {}, w; 
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
\* BEGIN TRANSLATION PCal-8c68717fa50233a5e0a592e1e248e9de
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
        /\ succs = {}
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
                 /\ succs' = {}
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
                                   /\ succs' = {}
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

\* END TRANSLATION TLA-8befcf14470ef67dababcf2fab7ead25

Correct == pc = "Done" => sccs = SCCs

StackEntry == [
   procedure : {"visit"},
   pc : {"continue_visit", "main"},
   succs : SUBSET Nodes,
   w : Nodes \cup {defaultInitValue},
   v : Nodes \cup {defaultInitValue}
]

TypeOK ==
  /\ index \in Nat
  /\ t_stack \in Seq(Nodes)
  /\ num \in [Nodes -> Nat \cup {-1}]
  /\ lowlink \in [Nodes -> Nat \cup {-1}]
  /\ onStack \in [Nodes -> BOOLEAN]
  /\ sccs \in SUBSET SUBSET Nodes
  /\ toVisit \in SUBSET Nodes
  /\ pc \in {"main", "Done", "start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"}
  /\ stack \in Seq(StackEntry)
  /\ succs \in SUBSET Nodes
  /\ v \in Nodes \cup {defaultInitValue}
  /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} => v \in Nodes
  /\ pc \in {"start_visit", "explore_succ", "visit_recurse", "continue_visit", "check_root"} => w \in Nodes 
  /\ w \in Nodes \cup {defaultInitValue}

USE SuccsType

THEOREM Spec => []TypeOK
<1>init. Init => TypeOK
  BY DEF Init, TypeOK
<1>next. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>. USE DEF TypeOK
  <2>1. CASE start_visit
    BY <2>1 DEF start_visit
  <2>2. CASE explore_succ
    BY <2>2 DEF vars, explore_succ
  <2>3. CASE visit_recurse
  <2>4. CASE continue_visit
    BY <2>4 DEF vars, continue_visit
  <2>5. CASE check_root
  <2>6. CASE main
  <2>7. CASE Terminating
    BY <2>7 DEF vars, Terminating
  <2>8. CASE UNCHANGED vars
    BY <2>8 DEF vars
  <2>9. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8 DEF Next, visit
<1>. QED  BY <1>init, <1>next, PTL DEF Spec

=============================================================================
\* Modification History
\* Last modified Tue Mar 03 20:28:45 CET 2020 by Angela Ipseiz
\* Last modified Tue Mar 03 11:04:54 CET 2020 by Angela Ipseiz
\* Last modified Thu Feb 27 16:24:13 CET 2020 by merz
\* Created Thu Feb 20 14:43:38 CET 2020 by merz
