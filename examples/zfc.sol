/*

Propositional Calculus:

Postulate rules for forming formulas, using negation and implication. Then
add the axioms for propositional calculus. These are axioms P2, P3, and P4
as shown in:
  https://en.wikipedia.org/wiki/Hilbert_system.
Axiom P1 is proven as `identity`. We then extend our system to include the
connectives "if and only if", "or", and "and".

*/
namespace
prop
{
  judgement
  is_formula(phi);

  judgement
  has_proof(phi);

  axiom
  WF_negation(phi)
  {
    assume is_formula(\$phi\);

    infer is_formula(\not $phi\);
  }

  axiom
  WF_implication(phi, psi)
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
  _simplification(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\($phi implies ($psi implies $phi))\);
  }

  theorem
  simplification(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\($phi implies ($psi implies $phi))\);
    infer is_formula(\($psi implies $phi)\);
    infer is_formula(\($phi implies ($psi implies $phi))\);

    step _simplification(\$phi\, \$psi\);
    step WF_implication(\$psi\, \$phi\);
    step WF_implication(\$phi\, \($psi implies $phi)\);
  }

  axiom
  _distributive(phi, psi, chi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume is_formula(\$chi\);

    infer has_proof(\(($phi implies ($psi implies $chi)) implies
      (($phi implies $psi) implies ($phi implies $chi)))\);
  }

  theorem
  distributive(phi, psi, chi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume is_formula(\$chi\);

    infer has_proof(\(($phi implies ($psi implies $chi)) implies
      (($phi implies $psi) implies ($phi implies $chi)))\);
    infer is_formula(\($psi implies $chi)\);
    infer is_formula(\($phi implies ($psi implies $chi))\);
    infer is_formula(\($phi implies $psi)\);
    infer is_formula(\($phi implies $chi)\);
    infer is_formula(\(($phi implies $psi) implies ($phi implies $chi))\);
    infer is_formula(\(($phi implies ($psi implies $chi)) implies
      (($phi implies $psi) implies ($phi implies $chi)))\);

    step _distributive(\$phi\, \$psi\, \$chi\);
    step WF_implication(\$psi\, \$chi\);
    step WF_implication(\$phi\, \($psi implies $chi)\);
    step WF_implication(\$phi\, \$psi\);
    step WF_implication(\$phi\, \$chi\);
    step WF_implication(\($phi implies $psi)\, \($phi implies $chi)\);
    step WF_implication(\($phi implies ($psi implies $chi))\,
      \(($phi implies $psi) implies ($phi implies $chi))\);
  }

  axiom
  _transposition(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\((not $psi implies not $phi)
      implies ($phi implies $psi))\);
  }

  theorem
  transposition(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\((not $psi implies not $phi)
      implies ($phi implies $psi))\);
    infer is_formula(\not $psi\);
    infer is_formula(\not $phi\);
    infer is_formula(\(not $psi implies not $phi)\);
    infer is_formula(\($phi implies $psi)\);
    infer is_formula(\((not $psi implies not $phi)
      implies ($phi implies $psi))\);

    step _transposition(\$phi\, \$psi\);
    step WF_negation(\$psi\);
    step WF_negation(\$phi\);
    step WF_implication(\not $psi\, \not $phi\);
    step WF_implication(\$phi\, \$psi\);
    step WF_implication(\(not $psi implies not $phi)\, \($phi implies $psi)\);
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

    step WF_implication(\$psi\, \$chi\);
    step modus_ponens(\$phi\, \($psi implies $chi)\);
    step modus_ponens(\$psi\, \$chi\);
  }

  theorem
  identity(phi)
  {
    assume is_formula(\$phi\);

    infer has_proof(\($phi implies $phi)\);

    step WF_implication(\$phi\, \$phi\);
    step simplification(\$phi\, \($phi implies $phi)\);
    step distributive(\$phi\, \($phi implies $phi)\, \$phi\);
    step modus_ponens(\($phi implies (($phi implies $phi) implies $phi))\,
      \(($phi implies ($phi implies $phi)) implies ($phi implies $phi))\);
    step simplification(\$phi\, \$phi\);
    step modus_ponens(\($phi implies ($phi implies $phi))\,
      \($phi implies $phi)\);
  }

  axiom
  WF_biconditional(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer is_formula(\($phi iff $psi)\);
  }

  axiom
  _D_biconditional(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\not ((($phi iff $psi) implies not (($phi implies $psi)
      implies not ($psi implies $phi))) implies not
      ((not (($phi implies $psi) implies not
      ($psi implies $phi))) implies ($phi iff $psi)))\);
  }

  theorem
  D_biconditional(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\not ((($phi iff $psi) implies not (($phi implies $psi)
      implies not ($psi implies $phi))) implies not
      ((not (($phi implies $psi) implies not
      ($psi implies $phi))) implies ($phi iff $psi)))\);

    step _D_biconditional(\$phi\, \$psi\);
  }

  theorem
  biconditional_to_implication(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(($phi iff $psi) implies ($phi implies $psi))\);
  }

  axiom
  WF_and(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer is_formula(\($phi and $psi)\);
  }

  axiom
  _D_and(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(($phi and $psi) iff not ($phi implies not $psi))\);
  }

  theorem
  D_and(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(($phi and $psi) iff not ($phi implies not $psi))\);
    infer is_formula(\($phi and $psi)\);
    infer is_formula(\not $psi\);
    infer is_formula(\($phi implies not $psi)\);
    infer is_formula(\not ($phi implies not $psi)\);
    infer is_formula(\(($phi and $psi) iff not ($phi implies not $psi))\);

    step _D_and(\$phi\, \$psi\);
    step WF_and(\$phi\, \$psi\);
    step WF_negation(\$psi\);
    step WF_implication(\$phi\, \not $psi\);
    step WF_negation(\($phi implies not $psi)\);
    step WF_biconditional(\($phi and $psi)\, \not ($phi implies not $psi)\);
  }

  axiom
  WF_or(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer is_formula(\($phi or $psi)\);
  }

  axiom
  _D_or(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(($phi or $psi) iff (not $phi implies $psi))\);
  }

  theorem
  D_or(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(($phi or $psi) iff (not $phi implies $psi))\);
    infer is_formula(\($phi or $psi)\);
    infer is_formula(\not $phi\);
    infer is_formula(\(not $phi implies $psi)\);
    infer is_formula(\(($phi or $psi) iff (not $phi implies $psi))\);

    step _D_or(\$phi\, \$psi\);
    step WF_or(\$phi\, \$psi\);
    step WF_negation(\$phi\);
    step WF_implication(\not $phi\, \$psi\);
    step WF_biconditional(\($phi or $psi)\, \(not $phi implies $psi)\);
  }
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

  axiom
  WF_existential(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    infer is_formula(\exists $x $phi\);
  }

  axiom
  _D_existential(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    infer has_proof(\(exists $x $phi iff not any $x not $phi)\);
  }

  theorem
  D_existential(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    infer has_proof(\(exists $x $phi iff not any $x not $phi)\);
    infer is_formula(\not $phi\);
    infer is_formula(\any $x not $phi\);
    infer is_formula(\not any $x not $phi\);
    infer is_formula(\exists $x $phi\);
    infer is_formula(\(exists $x $phi iff not any $x not $phi)\);

    step _D_existential(\$x\, \$phi\);
    step WF_negation(\$phi\);
    step universal_quantification(\$x\, \not $phi\);
    step WF_negation(\any $x not $phi\);
    step WF_existential(\$x\, \$phi\);
    step WF_biconditional(\exists $x $phi\, \not any $x not $phi\);
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
  WF_membership(x, y)
  {
    assume is_term(\$x\);
    assume is_term(\$y\);

    infer is_formula(\$x in $y\);
  }

  axiom
  A_extensionality(x, y, z)
  {
    assume is_variable(\$x\);
    assume is_variable(\$y\);
    assume is_variable(\$z\);

    infer has_proof(\any $x any $y
      (any $z ($z in $x iff $z in $y) implies $x = $y)\);
  }

  axiom
  WF_subset(x, y)
  {
    assume is_term(\$x\);
    assume is_term(\$y\);

    infer is_formula(\$x subset $y\);
  }

  axiom
  D_subset(x, y, z)
  {
    assume is_variable(\$x\);
    assume is_variable(\$y\);
    assume is_variable(\$z\);

    infer has_proof(\($x subset $y iff any $z ($z in $x implies $z in $y))\);
  }

/*
  theorem mutual_subsets(x, y)
  {
    assume is_variable(\$x\);
    assume is_variable(\$y\);

    infer has_proof(\(any $x any $y
      ($x = $y iff ($x subset $y and $y subset $x))\);
  }
*/
}
