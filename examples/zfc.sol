/*

Propositional Calculus:

Define rules for forming formulas, such as negation and implication. Then
add the axioms for propositional calculus.

*/
namespace
prop
{
  type Formula;

  def Formula
  not(phi: Formula);

  def Formula
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
    step conclusion_2 modus_ponens(phi, major);
    step conclusion modus_ponens(psi, major_2);
  }

  theorem
  identity(phi: Formula)
  {
    infer implies(phi, phi);

    let p1 implies(implies(implies(phi, phi), phi), implies(phi, phi));

    step s1 simplification(phi, implies(phi, phi));
    step s2 distributive(phi, implies(phi, phi), phi);
    step s3 modus_ponens(s1, p1);
    step s4 simplification(phi, phi);
    step conclusion modus_ponens(implies(phi, implies(phi, phi)),
      implies(phi, phi));
  }

  def Formula
  or(phi: Formula, psi: Formula)
  {
    implies(not(phi), psi);
  }

  def Formula
  and(phi: Formula, psi: Formula)
  {
    not(implies(phi, not(psi)));
  }

  def Formula
  iff(phi: Formula, psi: Formula)
  {
    and(implies(phi, psi), implies(psi, phi));
  }
}

/*

First Order Logic (with Equality):

*/
namespace
pred
{
  import prop;

  type Var;
  type Term;

  def Formula [x]
  any(x: Var, phi: Formula);

  def Formula [x]
  exists(x: Var, phi: Formula)
  {
    not(any(x, not(phi)));
  }

  axiom
  instantiation(x: Var, t: Term, phi: Formula)
  {
    require x free in phi;
    infer implies(any(x, phi), phi[x=t]);
  }

  axiom
  quantified_implication(x: Var, phi: Formula, psi: Formula)
  {
    infer implies(any(x, implies(phi, psi)), implies(any(x, phi),
      any(x, psi)));
  }

  axiom
  generalization(x: Var, phi: Formula)
  {
    require x bound in phi;
    infer implies(phi, any(x, phi));
  }

  def Formula
  eq(x: Var, y: Var);

  axiom
  identity2(x: Var)
  {
    infer eq(x, x);
  }

  axiom
  equality_substitution(x: Var, y: Var, z: Var, phi: Formula)
  {
    infer implies(eq(x, y), implies(phi[z=x], phi[z=y]));
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
