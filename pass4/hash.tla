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
variable x, rpcs = HashKey \X HashValue \X ClientOps;
begin
worker_begin:
    while Cardinality(rpcs)>0
    do
        \* r local to CHOOSE only
	x := CHOOSE r \in rpcs: TRUE;
        rpcs := rpcs \ {x};
	call PerformOp(x[1], x[2], x[3]);
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "4b6f0ae" /\ chksum(tla) = "5bb06a12") PCal-782ae353228cc15170c4590ec7433f1f
CONSTANT defaultInitValue
VARIABLES Hash, pc, stack, k_in, v_in, op_in, x, rpcs

vars == << Hash, pc, stack, k_in, v_in, op_in, x, rpcs >>

ProcSet == (1..1)

Init == (* Global variables *)
        /\ Hash = [hashKey \in HashKey |-> Nil]
        (* Procedure PerformOp *)
        /\ k_in = [ self \in ProcSet |-> defaultInitValue]
        /\ v_in = [ self \in ProcSet |-> defaultInitValue]
        /\ op_in = [ self \in ProcSet |-> defaultInitValue]
        (* Process Worker *)
        /\ x = [self \in 1..1 |-> defaultInitValue]
        /\ rpcs = [self \in 1..1 |-> HashKey \X HashValue \X ClientOps]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "worker_begin"]

perform_op_begin(self) == /\ pc[self] = "perform_op_begin"
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
                          /\ UNCHANGED << x, rpcs >>

PerformOp(self) == perform_op_begin(self)

worker_begin(self) == /\ pc[self] = "worker_begin"
                      /\ IF Cardinality(rpcs[self])>0
                            THEN /\ x' = [x EXCEPT ![self] = CHOOSE r \in rpcs[self]: TRUE]
                                 /\ rpcs' = [rpcs EXCEPT ![self] = rpcs[self] \ {x'[self]}]
                                 /\ /\ k_in' = [k_in EXCEPT ![self] = x'[self][1]]
                                    /\ op_in' = [op_in EXCEPT ![self] = x'[self][3]]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "PerformOp",
                                                                             pc        |->  "worker_begin",
                                                                             k_in      |->  k_in[self],
                                                                             v_in      |->  v_in[self],
                                                                             op_in     |->  op_in[self] ] >>
                                                                         \o stack[self]]
                                    /\ v_in' = [v_in EXCEPT ![self] = x'[self][2]]
                                 /\ pc' = [pc EXCEPT ![self] = "perform_op_begin"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << stack, k_in, v_in, op_in, x, 
                                                 rpcs >>
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
