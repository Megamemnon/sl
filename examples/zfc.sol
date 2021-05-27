/*

SOL Language Cheatsheet:

SOL is a small metalanguage for working with mathematical logic.

SCOPING:
Create a namespace with:
``
namespace
[NAMESPACE_NAME]
{
  [DECLARATIONS]
}
``
Declarations `[DECLARATION]` within a namespace can be accessed
by `[NAMESPACE_NAME].[DECLARATION]`. Namespaces may be nested.

FORMULAS:
To declare a schema for a valid formula, write:
``
formula
[FORMULA_NAME]([FORMULA_1], ..., [FORMULA_N])
{
  [FORMULA];
}
``
The parameters can take any valid identifier name, and the formula is just
a string where formulas will be substituted as parameters.

RULES OF INFERENCE:
Postulate a rule of inference, with the hypothesis that
`[HYPOTHESIS_1]`, ..., `[HYPOTHESIS_M]` are provable formulas in
`[FORMULA_1]`, ..., `[FORMULA_N]`, and that `[FORMULA]` is
consequently provable.
``
rule
[RULE_NAME]([FORMULA_1], ..., [FORMULA_N])
{
  hypothesis [HYPOTHESIS_1_NAME] [HYPOTHESIS_1];
  ...
  hypothesis [HYPOTHESIS_M_NAME] [HYPOTHESIS_M];
  infer [FORMULA];
}
``

AXIOMS:
Postulate an axiom (a formula that is assumed to have a proof). The axiom
is just a formula in the variables `[VAR_1]`, ..., `[VAR_N]`.
``
axiom
[AXIOM_NAME]([VAR_1], ..., [VAR_N])
{
  [FORMULA];
}
``

THEOREMS:
To state and prove a theorem, with the hypotheses
`[HYPOTHESIS_1]`, ..., `[HYPOTHESIS_M]` that are formulas in
`[FORMULA_1]`, ..., `[FORMULA_N]`, and the consequent `[FORMULA]`, write:
``
theorem
[THEOREM_NAME]([FORMULA_1], ..., [FORMULA_N])
{
  hypothesis [HYPOTHESIS_1_NAME] [HYPOTHESIS_1];
  ...
  hypothesis [HYPOTHESIS_M_NAME] [HYPOTHESIS_M];
  infer [FORMULA];
}
``

*/

/*

Propositional Calculus:

Define rules for forming formulas, such as negation and implication. Then
add the axioms for propositional calculus.

*/

namespace
prop
{

  formula
  not(phi)
  {
    not phi;
  }

  formula
  implies(phi, psi)
  {
    (phi implies psi);
  }

  rule
  modus_ponens(phi, psi)
  {
    hypothesis minor phi;
    hypothesis major (phi implies psi);
    infer psi;
  }

  axiom
  simplification(phi, psi)
  {
    (phi implies (psi implies phi));
  }

  axiom
  distributive(psi, phi, chi)
  {
    ((phi implies (psi implies chi)) implies
      ((phi implies psi) implies (phi implies chi)));
  }

  axiom
  transposition(phi, psi)
  {
    ((not psi implies not phi) implies (phi implies psi));
  }

  theorem
  double_modus_ponens(phi, psi, chi)
  {
    hypothesis minor_1 phi;
    hypothesis minor_2 psi;
    hypothesis major (phi implies (psi implies chi))
    infer chi;

    formula major_2 implies(psi, chi); // (psi implies chi)
    step conclusion_2 modus_ponens(phi, major)[_minor=phi, _major=major]; // prove major_2
    step conclusion modus_ponens(psi, major_2)[_minor=psi, _major=major_2]; // prove the conclusion
  }

}

/*

First Order Logic:

*/


/*
axiom
zfc-extensionality(x, y, &z)
{
  any x any y [any z(z in x iff z in y) implies x = y].
}

axiom
zfc-regularity(x, y, &a)
{
  any x [exists a (a in x) implies exists y (y in x and not exists z (
    z in y and z in x))].
}

axiomschema
zfc-specification(x, z)
{

}

/* TODO: Is the axiom of pairing necessary? It can be proved as a theorem from
   the rest of ZFC. */

*/
axiom
zfc-pairing()
{

}

axiom
zfc-union(F)
{
  any F exists A any Y any x [(x in Y and Y in F) implies x in A].
}

axiomschema
zfc-replacement()
{

}

axiom
zfc-infinity()
{

}

axiom
zfc-power-set()
{

}

axiom
zfc-well-ordering()
{

}
*/
