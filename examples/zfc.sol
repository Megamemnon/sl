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
[FORMULA_NAME]([VAR_1], ..., [VAR_N])
{
  [FORMULA];
}
``
The parameters can take any valid identifier name, and the formula is just
a string where variables will be substituted as parameters.

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
  not(phi: Formula);

  formula
  implies(phi: Formula, psi: Formula);

  rule
  modus_ponens(phi, psi)
  {
    hypothesis minor phi;
    hypothesis major implies(phi, psi);
    infer psi;
  }

  axiom
  simplification(phi, psi)
  {
    implies(phi, implies(psi, phi));
  }

  axiom
  distributive(psi, phi, chi)
  {
    implies(implies(phi, implies(psi, chi)),
      implies(implies(phi, psi), implies(phi, chi)));
  }

  axiom
  transposition(phi, psi)
  {
    implies(implies(not(psi), not(phi)),
      implies(phi, psi));
  }

  theorem
  double_modus_ponens(phi, psi, chi)
  {
    hypothesis minor_1 phi;
    hypothesis minor_2 psi;
    hypothesis major implies(phi, implies(psi, chi));
    infer chi;

    formula major_2 implies(psi, chi);
    step conclusion_2 modus_ponens(phi, major)[_minor=phi, _major=major, _infer=major_2];
    step conclusion modus_ponens(psi, major_2)[_minor=psi, _major=major_2, _infer=chi];
  }

  formula
  or(phi: Formula, psi: Formula)
  {
    implies(not(phi), psi);
  }

  formula
  and(phi: Formula, psi: Formula)
  {
    not(implies(phi, not(psi)));
  }

  formula
  iff(phi: Formula, psi: Formula)
  {
    and(implies(phi, psi), implies(psi, phi));
  }
}

/*

First Order Logic:

*/
namespace
pred
{
  import prop;

  formula
  univ(x: Var, phi: Formula);

  formula
  exists(x: Var, phi: Formula)
  {
    not(any(x, not(phi)));
  }

  rule
  generalization(phi: Formula)
  {
    hypothesis main phi;
    infer univ(x, phi);
  }
}

/*

ZFC Set Theory:

TODO: Use quantifiers instead of metavariables for ZFC axioms?

*/
namespace
zfc
{

  import prop, pred;

  formula
  in(x, y);

  formula
  subset(x, y)
  {
    any(z, implies(in(z, x), in(z, y)));
  }

  formula
  eq(x, y);

  axiom
  extensionality(x, y)
  {
    implies(any(z, iff(in(z, x), in(z, y))), eq(x, y));
  }

  formula
  empty(x)
  {
    any(z, not(in(z, x)));
  }

}
