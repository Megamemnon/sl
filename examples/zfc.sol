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

  axiom
  modus_ponens(phi: Formula, psi: Formula)
  {
    hypothesis minor phi;
    hypothesis major implies(phi, psi);
    infer psi;
  }

  axiom
  simplification(phi: Formula, psi: Formula)
  {
    infer implies(phi, implies(psi, phi));
  }

  axiom
  distributive(psi: Formula, phi: Formula, chi: Formula)
  {
    infer implies(implies(phi, implies(psi, chi)),
      implies(implies(phi, psi), implies(phi, chi)));
  }

  axiom
  transposition(phi: Formula, psi: Formula)
  {
    infer implies(implies(not(psi), not(phi)), implies(phi, psi));
  }

  theorem
  double_modus_ponens(phi: Formula, psi: Formula, chi: Formula)
  {
    hypothesis minor_1 phi;
    hypothesis minor_2 psi;
    hypothesis major implies(phi, implies(psi, chi));
    infer chi;

    let major_2 implies(psi, chi);
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
  any(x: Var, phi: Formula);

  formula
  exists(x: Var, phi: Formula)
  {
    not(any(x, not(phi)));
  }

  /* Convenience */

  formula
  any_2(x: Var, y: Var, phi: Formula)
  {
    any(x, any(y, phi));
  }

  axiom
  generalization(phi: Formula)
  {
    hypothesis main phi;
    infer any(x, phi);
  }
}

/*

ZFC Set Theory:

*/
namespace
zfc
{

  import prop, pred;

  formula
  in(x: Var, y: Var);

  formula
  subset(x: Var, y: Var)
  {
    any(z, implies(in(z, x), in(z, y)));
  }

  formula
  eq(x: Var, y: Var);

  axiom
  extensionality()
  {
    infer any2(x, y, implies(any(z, iff(in(z, x), in(z, y))), eq(x, y)));
  }

  formula
  empty(x: Var)
  {
    any(z, not(in(z, x)));
  }

}
