/*

Propositional Calculus:

Define rules for forming formulas, using negation and implication. Then
add the axioms for propositional calculus. Finally, utility theorems are
proven.

*/
namespace
prop
{
  judgement
  is_formula(phi);

  judgement
  has_proof(phi);

  axiom
  negation(phi)
  {
    assume is_formula(\$phi\);

    infer is_formula(\not $phi\);
  }

  axiom
  implication(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer is_formula(\($phi implies $psi)\);
  }

  axiom
  modus_ponens(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    assume has_proof(\$phi\);
    assume has_proof(\($phi implies $psi)\);

    infer has_proof(\$psi\);
  }

  axiom
  simplification(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\($phi implies ($psi implies $phi))\);
  }

  axiom
  distributive(phi, psi, chi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume is_formula(\$chi\);

    infer has_proof(\(($phi implies ($psi implies $chi)) implies
      (($phi implies $psi) implies ($phi implies $chi)))\);
  }

  axiom
  transposition(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\((not $psi implies not $phi)
      implies ($phi implies $psi))\);
  }

  theorem
  double_modus_ponens(phi, psi, chi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume is_formula(\$chi\);

    assume has_proof(\$phi\);
    assume has_proof(\$psi\);
    assume has_proof(\($phi implies ($psi implies $chi))\);

    infer has_proof(\$chi\);

    step implication(\$psi\, \$chi\);
    step modus_ponens(\$phi\, \($psi implies $chi)\);
    step modus_ponens(\$psi\, \$chi\);
  }

/*
  theorem
  identity(phi)
  {
    infer has_proof(implies(phi, phi));

    step p1 implies(implies(implies(phi, phi), phi), implies(phi, phi));

    step s1 simplification(phi, implies(phi, phi));
    step s2 distributive(phi, implies(phi, phi), phi);
    step s3 modus_ponens(s1, p1);
    step s4 simplification(phi, phi);
    step conclusion modus_ponens(implies(phi, implies(phi, phi)),
      implies(phi, phi));
  }

  expression Formula
  or(phi: Formula, psi: Formula)
  {
    implies(not(phi), psi);
  }

  expression Formula
  and(phi: Formula, psi: Formula)
  {
    not(implies(phi, not(psi)));
  }

  expression Formula
  iff(phi: Formula, psi: Formula)
  {
    and(implies(phi, psi), implies(psi, phi));
  }
*/

}

/*

First Order Logic (with Equality):

Define terms, variables, and quantification. After developing the rules
for free and bound variables, add the axioms for first order logic with
equality. Then prove utility theorems.

*/
namespace
pred
{
  import prop;

  judgement
  is_term(t);

  judgement
  is_variable(x);

  axiom
  variables_are_terms(x)
  {
    assume is_variable(\$x\);

    infer is_term(\$x\);
  }

  axiom
  universal_quantification(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    infer is_formula(\any $x $phi\);
  }

  judgement
  bound_in(x, phi);

  judgement
  free_in(x, phi);

  judgement
  is_atomic_formula(phi);

  axiom
  free_atomic(x, phi)
  {
    assume is_variable(\$x\);
    assume is_atomic_formula(\$phi\);

    assume subexpression(\$x\, \$phi\);

    infer free_in(\$x\, \$phi\);
  }

  axiom
  bound_negation(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    assume bound_in(\$x\, \$phi\);

    infer bound_in(\$x\, \not $phi\);
  }

  axiom
  free_negation(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    assume free_in(\$x\, \$phi\);

    infer free_in(\$x\, \not $phi\);
  }

  axiom
  bound_implication_1(x, phi, psi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    assume bound_in(\$x\, \$phi\);

    infer bound_in(\$x\, \($phi implies $psi)\);
  }

  axiom
  bound_implication_2(x, phi, psi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    assume bound_in(\$x\, \$psi\);

    infer bound_in(\$x\, \($phi implies $psi)\);
  }

  axiom
  free_implication_1(x, phi, psi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    assume free_in(\$x\, \$phi\);

    infer free_in(\$x\, \($phi implies $psi)\);
  }

  axiom
  free_implication_2(x, phi, psi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    assume free_in(\$x\, \$psi\);

    infer free_in(\$x\, \($phi implies $psi)\);
  }

  axiom
  free_universal(x, y, phi)
  {
    assume is_variable(\$x\);
    assume is_variable(\$y\);
    assume is_formula(\$phi\);

    assume free_in(\$x\, \$phi\);
    assume distinct(\$x\, \$y\);

    infer free_in(\$x\, \any $y $phi\);
  }

  axiom
  bound_universal_1(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    infer bound_in(\$x\, \any $x $phi\);
  }

  axiom
  bound_universal_2(x, y, phi)
  {
    assume is_variable(\$x\);
    assume is_variable(\$y\);
    assume is_formula(\$phi\);

    assume bound_in(\$x\, \$phi\);

    infer bound_in(\$x\, \any $y $phi\);
  }

/*
  expression Formula
  exists(x: Var, phi: Formula)
  {
    not(any(x, not(phi)));
  }
*/

  axiom
  instantiation(x, t, phi)
  {
    assume is_variable(\$x\);
    assume is_term(\$t\);
    assume is_formula(\$phi\);

    assume free_in(\$t\, \$phi\);

    infer has_proof(\(any $x $phi implies $phi[x=\$t\])\);
  }

  axiom
  quantified_implication(x, phi, psi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(any $x ($phi implies $psi)) implies (any $x $phi
      implies any $x $psi))\);
  }

  axiom
  generalization(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    assume bound_in(\$x\, \$phi\);

    infer has_proof(\($phi implies any $x $phi)\);
  }

  axiom
  equality(x, y)
  {
    assume is_term(\$x\);
    assume is_term(\$y\);

    infer is_formula(\$x = $y\);
  }

  axiom
  equality_reflexive(x)
  {
    assume is_variable(\$x\);

    infer has_proof(\$x = $x\);
  }

  axiom
  equality_substitution(x, y, z, phi)
  {
    assume is_term(\$x\);
    assume is_term(\$y\);
    assume is_variable(\$z\);
    assume is_formula(\$phi\);

    infer has_proof(\($x = $y implies ($phi[z=\$x\] implies $phi[z=\$y\]))\);
  }
}

/*

ZFC Set Theory:

*/
namespace
zfc
{
  import prop, pred;

  axiom
  membership(x, y)
  {
    assume is_term(\$x\);
    assume is_term(\$y\);

    infer is_formula(\$x in $y\);
  }

/*
  formula
  subset(x: Term, y: Term)
  {
    any(z, implies(in(z, x), in(z, y)));
  }

  axiom
  extensionality()
  {
    infer any2(x, y, implies(any(z, iff(in(z, x), in(z, y))), eq(x, y)));
  }

  formula
  empty(x: Term)
  {
    any(z, not(in(z, x)));
  }
*/
}
