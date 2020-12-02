----------------------------- MODULE term -----------------------------
EXTENDS     Integers, Sequences, FiniteSets, TLC

(*--algorithm junk
    
variables
    Queue = <<>>,

\* 1 Consumer process with self=1
\* e.g. there is only one integer
\* in range 1..1 namely 1
fair process Consumer \in 1..1
begin
consumer_begin:
    while (TRUE)
    do
        \* block until queue non-empty
        await Queue /= <<>>;
        \* remove first element
        Queue := Tail(Queue);
    end while;
end process;

\* 1 Producer process with self=2
fair process Producer \in 2..2
begin
producer_begin:
    while (TRUE)
    do
      with v \in 1..2
      do
        \* append 'v' to 'Queue'
        Queue := Queue \o <<v>>;
      end with;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "1ee56825" /\ chksum(tla) = "2ce55602") PCal-782ae353228cc15170c4590ec7433f1f
VARIABLES Queue, pc

vars == << Queue, pc >>

ProcSet == (1..1) \cup (2..2)

Init == (* Global variables *)
        /\ Queue = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in 1..1 -> "consumer_begin"
                                        [] self \in 2..2 -> "producer_begin"]

consumer_begin(self) == /\ pc[self] = "consumer_begin"
                        /\ Queue /= <<>>
                        /\ Queue' = Tail(Queue)
                        /\ pc' = [pc EXCEPT ![self] = "consumer_begin"]

Consumer(self) == consumer_begin(self)

producer_begin(self) == /\ pc[self] = "producer_begin"
                        /\ \E v \in 1..2:
                             Queue' = Queue \o <<v>>
                        /\ pc' = [pc EXCEPT ![self] = "producer_begin"]

Producer(self) == producer_begin(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..1: Consumer(self))
           \/ (\E self \in 2..2: Producer(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..1 : WF_vars(Consumer(self))
        /\ \A self \in 2..2 : WF_vars(Producer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION  TLA-c917aaec6384b558d53d8d37d1bdcac0

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-617dce1dfc71fada07ed9b521b0fdffd
=============================================================================
\* Modification History
\* Last modified Tue Nov 24 15:39:56 EST 2020 by smiller
\* Created Sun Nov 08 20:07:06 EST 2020 by smiller
