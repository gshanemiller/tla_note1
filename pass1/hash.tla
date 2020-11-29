----------------------------- MODULE hash -----------------------------
EXTENDS     Integers, Sequences, FiniteSets, TLC
CONSTANTS   HashKey, HashValue, ClientOps, Nil

(*--algorithm junk
    
variables
    Hash = [hashKey \in HashKey |-> Nil],

procedure PerformOp(k_in,v_in,op_in)
begin
perform_op_begin:
    \* print <<k_in,v_in,op_in>>;
    if op_in=0
    then
        skip;
    elsif op_in=1
    then
        Hash[k_in]:=v_in;
    else
	\* delete
        Hash[k_in]:=Nil;
    end if;
    return;
end procedure;

fair process Worker \in 1..1
begin
worker_begin:
    while (TRUE)
    do
      with k \in HashKey, v \in HashValue, op \in ClientOps
      do
          call PerformOp(k,v,op)
      end with;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "f020b36a" /\ chksum(tla) = "5a67e9fc") PCal-782ae353228cc15170c4590ec7433f1f
CONSTANT defaultInitValue
VARIABLES Hash, pc, stack, k_in, v_in, op_in

vars == << Hash, pc, stack, k_in, v_in, op_in >>

ProcSet == (1..1)

Init == (* Global variables *)
        /\ Hash = [hashKey \in HashKey |-> Nil]
        (* Procedure PerformOp *)
        /\ k_in = [ self \in ProcSet |-> defaultInitValue]
        /\ v_in = [ self \in ProcSet |-> defaultInitValue]
        /\ op_in = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "worker_begin"]

perform_op_begin(self) == /\ pc[self] = "perform_op_begin"
                          /\ PrintT(<<k_in[self],v_in[self],op_in[self]>>)
                          /\ IF op_in[self]=0
                                THEN /\ TRUE
                                     /\ Hash' = Hash
                                ELSE /\ IF op_in[self]=1
                                           THEN /\ Hash' = [Hash EXCEPT ![k_in[self]] = v_in[self]]
                                           ELSE /\ Hash' = [Hash EXCEPT ![k_in[self]] = Nil]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ k_in' = [k_in EXCEPT ![self] = Head(stack[self]).k_in]
                          /\ v_in' = [v_in EXCEPT ![self] = Head(stack[self]).v_in]
                          /\ op_in' = [op_in EXCEPT ![self] = Head(stack[self]).op_in]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]

PerformOp(self) == perform_op_begin(self)

worker_begin(self) == /\ pc[self] = "worker_begin"
                      /\ \E k \in HashKey:
                           \E v \in HashValue:
                             \E op \in ClientOps:
                               /\ /\ k_in' = [k_in EXCEPT ![self] = k]
                                  /\ op_in' = [op_in EXCEPT ![self] = op]
                                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "PerformOp",
                                                                           pc        |->  "worker_begin",
                                                                           k_in      |->  k_in[self],
                                                                           v_in      |->  v_in[self],
                                                                           op_in     |->  op_in[self] ] >>
                                                                       \o stack[self]]
                                  /\ v_in' = [v_in EXCEPT ![self] = v]
                               /\ pc' = [pc EXCEPT ![self] = "perform_op_begin"]
                      /\ Hash' = Hash

Worker(self) == worker_begin(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: PerformOp(self))
           \/ (\E self \in 1..1: Worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..1 : WF_vars(Worker(self)) /\ WF_vars(PerformOp(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION  TLA-c917aaec6384b558d53d8d37d1bdcac0

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-617dce1dfc71fada07ed9b521b0fdffd
=============================================================================
\* Modification History
\* Last modified Tue Nov 24 15:39:56 EST 2020 by smiller
\* Created Sun Nov 08 20:07:06 EST 2020 by smiller
