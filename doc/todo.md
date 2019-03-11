# To-Do List

- Rewrite instantiate_assertion, instantiate_predicate, and
  instantiate_term to implement seperate, capture-avoiding substitution.
  NOTE: It may be necessary to use the locally nameless representation
  for assertions as well as terms.  This would, however, make assertions
  less legible and cause terms to contain parameters that are not
  locally bound.
- Ensure the freshness of variable names in the DS{ForAll,Exists}{P,C}
  rules.
- Fix existing SL_{1,2} theorem proofs.
  NOTE: Fixing the SL_1 proof will require changes to term evaluation.
  This is because the proof evaluates a match term where the term being
  destructed is a free variable and the alternative case is failure.  If
  terms were typed, the alternative case would be unnecessary because
  the match would be exhaustive for the type of the free variable.  As
  things are now, matching on a free variable whose form is unknown
  causes the alternative case to be evaluated, in this case causing a
  failure.  The desired effect is to infer from the match term that the
  free variable must be of the given form, and proceed from there.
- Prove PL_{1,2,3} theorems.
- Make the assertion "exists:" notation variadic like the "forall:"
  notation.  Basing the notation on the forall notation produces scope
  errors.
- Make the d_{forall,exists}{p,c} tactics variadic so that multiple
  quantifiers can be introduced/specialized in one invocation.
- Add tactics for rewriting in both the premises and the conclusion.
  A pattern for rewriting can be seen in the current SL_{1,2} proofs.
  It should be possible to refactor this pattern into a tactic.
- Many proofs are Admitted.  These should be completed.
- Only a few derived rules are stated.  The rest should be added.
