Alethfeld Proof Workflow
========================

1. INITIALIZE
   af init --name "My Proof"
   af create --root --claim "Main theorem"

2. VERIFY (verifier role) - gatekeeper step
   af ready --name <you> --role verifier
   af vote <id> --for --reason "..."
   Options: vote for/against, request decomposition, request refinement

3. DECOMPOSE (proposer role)
   af ready --name <you> --role proposer
   af propose <id> --claim "substep 1" --claim "substep 2"

4. REVIEW (advisor role) - requires quorum approvals
   af ready --name <you> --role advisor
   af approve <id> --reason "..."
   af approve-all --reason "..."

5. VALIDATE
   af check   # Verify DAG integrity
   af tree 1  # View proof structure
   af status  # Overall progress
