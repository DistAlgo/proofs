1. PaxosLam.tla:
TLA+ specification of Basic Paxos as in
<https://github.com/tlaplus/v1-tlapm/blob/master/examples/paxos/Paxos.tla>.
Following modifications have been made to the file:

    1. Moved lemmas `QuorumNonEmpty` and `NoneNotAValue` after definition of `Spec`. This is done to get true specification line count easily.
      
    2. Commented the following:
        1. `chosenBar`, line 541
        2. `C`, line 543
        3. Theorem `Refinement`, line 549---567
      
       This is done because our goal is to prove Safety of the specification, not to prove that it also refines some other specification.

2. MultiPaxosFM16.tla:
TLA+ specification and proof of Multi-Paxos as described in \[1\].

3. MultiPaxos.tla:
An improved TLA+ specification and proof of Multi-Paxos compared to MultiPaxosFM16.tla. These improvements are described in \[2\].

4. MultiPaxosPreemptionFM16.tla:
TLA+ specification and proof of Multi-Paxos with Preemption
as described in \[1\].

5. MultiPaxosPreemption.tla:
An improved TLA+ specification and proof of Multi-Paxos with Preemption compared to MultiPaxosPreemptionFM16.tla. These improvements are described in \[2\].

# Notes
The MultiPaxos proofs in files *FM16.tla were checked using TLAPS version 1.5.3 and 1.5.6. The improved MultiPaxos proofs in other files were checked using version 1.5.6. A summary of the proof statistics are reported in \[2\].

# References
\[1\] Chand, S., Liu, Y. A., & Stoller, S. D. (2016, November). Formal Verification of Multi-Paxos for Distributed Consensus. In International Symposium on Formal Methods (pp. 119-136). [SpringerLink](https://link.springer.com/chapter/10.1007/978-3-319-48989-6_8)

\[2\] Chand, S., Liu, Y. A., & Stoller, S. D. (2019, January). Formal Verification of Multi-Paxos for Distributed Consensus. arXiv preprint arXiv:1606.01387. [arXiv](https://arxiv.org/abs/1606.01387)
