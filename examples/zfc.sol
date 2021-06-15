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

  /*

  Common theorems of propositional calculus, based on the list given in
  https://en.wikipedia.org/wiki/Hilbert_system

  */
  theorem
  identity(phi)
  {
    assume is_formula(\$phi\);

    infer is_formula(\($phi implies $phi)\);
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

  theorem
  hypothetical_syllogism(phi, psi, chi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume is_formula(\$chi\);

    infer has_proof(\(($psi implies $chi) implies
      (($phi implies $psi) implies ($phi implies $chi)))\);
    infer is_formula(\($psi implies $chi)\);
    infer is_formula(\($phi implies $psi)\);
    infer is_formula(\($phi implies $chi)\);
    infer is_formula(\(($phi implies $psi) implies ($phi implies $chi))\);
    infer is_formula(\(($psi implies $chi) implies
      (($phi implies $psi) implies ($phi implies $chi)))\);

    step WF_implication(\$psi\, \$chi\);
    step WF_implication(\$phi\, \$psi\);
    step WF_implication(\$phi\, \$chi\);
    step WF_implication(\($phi implies $psi)\, \($phi implies $chi)\);
    step WF_implication(\($psi implies $chi)\,
      \(($phi implies $psi) implies ($phi implies $chi))\);

    step distributive(\$phi\, \$psi\, \$chi\);
    step simplification(\(($phi implies ($psi implies $chi)) implies
      (($phi implies $psi) implies ($phi implies $chi)))\,
      \($psi implies $chi)\);
    step modus_ponens(\(($phi implies ($psi implies $chi)) implies
      (($phi implies $psi) implies ($phi implies $chi)))\,
      \(($psi implies $chi) implies (($phi implies ($psi implies $chi)) implies
      (($phi implies $psi) implies ($phi implies $chi))))\);
    step distributive(\($psi implies $chi)\,
      \($phi implies ($psi implies $chi))\,
      \(($phi implies $psi) implies ($phi implies $chi))\);
    step modus_ponens(\(($psi implies $chi) implies
      (($phi implies ($psi implies $chi)) implies
      (($phi implies $psi) implies ($phi implies $chi))))\,
      \((($psi implies $chi) implies ($phi implies ($psi implies $chi))) implies
      (($psi implies $chi) implies
      (($phi implies $psi) implies ($phi implies $chi))))\);
    step simplification(\($psi implies $chi)\, \$phi\);
    step modus_ponens(\(($psi implies $chi)
      implies ($phi implies ($psi implies $chi)))\,
      \(($psi implies $chi) implies
      (($phi implies $psi) implies ($phi implies $chi)))\);
  }

  theorem
  hypothetical_syllogism_meta(phi, psi, chi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume is_formula(\$chi\);
    assume has_proof(\($psi implies $chi)\);
    assume has_proof(\($phi implies $psi)\);

    infer has_proof(\($phi implies $chi)\);
    infer is_formula(\($phi implies $chi)\);

    step WF_implication(\$phi\, \$chi\);

    step hypothetical_syllogism(\$phi\, \$psi\, \$chi\);
    step modus_ponens(\($psi implies $chi)\,
      \(($phi implies $psi) implies ($phi implies $chi))\);
    step modus_ponens(\($phi implies $psi)\, \($phi implies $chi)\);
  }

  theorem
  double_simplification(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\($phi implies (($phi implies $psi) implies $psi))\);
    infer is_formula(\($phi implies $psi)\);
    infer is_formula(\(($phi implies $psi) implies $psi)\);
    infer is_formula(\($phi implies (($phi implies $psi) implies $psi))\);

    step WF_implication(\$phi\, \$psi\);
    step WF_implication(\($phi implies $psi)\, \$psi\);
    step WF_implication(\$phi\, \(($phi implies $psi) implies $psi)\);

    step distributive(\($phi implies $psi)\, \$phi\, \$psi\);
    step identity(\($phi implies $psi)\);
    step modus_ponens(\(($phi implies $psi) implies ($phi implies $psi))\,
      \((($phi implies $psi) implies $phi)
      implies (($phi implies $psi) implies $psi))\);
    step hypothetical_syllogism(\$phi\, \(($phi implies $psi) implies $phi)\,
      \(($phi implies $psi) implies $psi)\);
    step modus_ponens(\((($phi implies $psi) implies $phi)
      implies (($phi implies $psi) implies $psi))\,
      \(($phi implies (($phi implies $psi) implies $phi)) implies
      ($phi implies (($phi implies $psi) implies $psi)))\);
    step simplification(\$phi\, \($phi implies $psi)\);
    step modus_ponens(\($phi implies (($phi implies $psi) implies $phi))\,
      \($phi implies (($phi implies $psi) implies $psi))\);
  }

  theorem
  double_negation_left(phi)
  {
    assume is_formula(\$phi\);

    infer has_proof(\(not not $phi implies $phi)\);
    infer is_formula(\not $phi\);
    infer is_formula(\not not $phi\);
    infer is_formula(\(not not $phi implies $phi)\);

    step WF_negation(\$phi\);
    step WF_negation(\not $phi\);
    step WF_implication(\not not $phi\, \$phi\);

    step simplification(\$phi\, \$phi\); /* This can be any formula that is axiomatically true */
    step WF_negation(\($phi implies ($phi implies $phi))\);
    step transposition(\not $phi\, \not ($phi implies ($phi implies $phi))\);
    step transposition(\($phi implies ($phi implies $phi))\, \$phi\);
    step hypothetical_syllogism_meta(\(not not ($phi implies
      ($phi implies $phi)) implies not not $phi)\,
      \(not $phi implies not ($phi implies ($phi implies $phi)))\,
      \(($phi implies ($phi implies $phi)) implies $phi)\);
    step simplification(\not not $phi\,
      \not not ($phi implies ($phi implies $phi))\);
    step hypothetical_syllogism_meta(\not not $phi\,
      \(not not ($phi implies ($phi implies $phi)) implies not not $phi)\,
      \(($phi implies ($phi implies $phi)) implies $phi)\);
    step double_simplification(\($phi implies ($phi implies $phi))\, \$phi\);
    step modus_ponens(\($phi implies ($phi implies $phi))\,
      \((($phi implies ($phi implies $phi)) implies $phi) implies $phi)\);
    step hypothetical_syllogism_meta(\not not $phi\,
      \(($phi implies ($phi implies $phi)) implies $phi)\,
      \$phi\);
  }

  theorem
  double_negation_right(phi)
  {
    assume is_formula(\$phi\);

    infer has_proof(\($phi implies not not $phi)\);
    infer is_formula(\not $phi\);
    infer is_formula(\not not $phi\);
    infer is_formula(\($phi implies not not $phi)\);

    step WF_negation(\$phi\);
    step WF_negation(\not $phi\);
    step WF_implication(\$phi\, \not not $phi\);

    step double_negation_left(\not $phi\);
    step transposition(\$phi\, \not not $phi\);
    step modus_ponens(\(not not not $phi implies not $phi)\,
      \($phi implies not not $phi)\);
  }

  theorem
  implication_commutation(phi, psi, chi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume is_formula(\$chi\);

    infer has_proof(\(($phi implies ($psi implies $chi)) implies
      ($psi implies ($phi implies $chi)))\);
    infer is_formula(\($phi implies $chi)\);
    infer is_formula(\($psi implies $chi)\);
    infer is_formula(\($phi implies ($psi implies $chi))\);
    infer is_formula(\($psi implies ($phi implies $chi))\);
    infer is_formula(\(($phi implies ($psi implies $chi)) implies
      ($psi implies ($phi implies $chi)))\);

    step WF_implication(\$phi\, \$chi\);
    step WF_implication(\$psi\, \$chi\);
    step WF_implication(\$phi\, \($psi implies $chi)\);
    step WF_implication(\$psi\, \($phi implies $chi)\);
    step WF_implication(\($phi implies ($psi implies $chi))\,
      \($psi implies ($phi implies $chi))\);

    step distributive(\$phi\, \$psi\, \$chi\);
    step hypothetical_syllogism(\$psi\, \($phi implies $psi)\,
      \($phi implies $chi)\);
    step hypothetical_syllogism_meta(\($phi implies ($psi implies $chi))\,
      \(($phi implies $psi) implies ($phi implies $chi))\,
      \(($psi implies ($phi implies $psi)) implies
      ($psi implies ($phi implies $chi)))\);
    step distributive(\($phi implies ($psi implies $chi))\,
      \($psi implies ($phi implies $psi))\,
      \($psi implies ($phi implies $chi))\);
    step modus_ponens(\(($phi implies ($psi implies $chi)) implies
      (($psi implies ($phi implies $psi))
      implies ($psi implies ($phi implies $chi))))\,
      \((($phi implies ($psi implies $chi)) implies ($psi implies
      ($phi implies $psi))) implies (($phi implies ($psi implies $chi)) implies
      ($psi implies ($phi implies $chi))))\);
    step simplification(\$psi\, \$phi\);
    step simplification(\($psi implies ($phi implies $psi))\,
      \($phi implies ($psi implies $chi))\);
    step modus_ponens(\($psi implies ($phi implies $psi))\,
      \(($phi implies ($psi implies $chi)) implies
      ($psi implies ($phi implies $psi)))\);
    step modus_ponens(\(($phi implies ($psi implies $chi)) implies
      ($psi implies ($phi implies $psi)))\,
      \(($phi implies ($psi implies $chi)) implies
      ($psi implies ($phi implies $chi)))\);
  }

  theorem
  hypothetical_syllogism_2(phi, psi, chi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume is_formula(\$chi\);

    infer has_proof(\(($phi implies $psi) implies
      (($psi implies $chi) implies ($phi implies $chi)))\);
    infer is_formula(\($phi implies $psi)\);
    infer is_formula(\($psi implies $chi)\);
    infer is_formula(\($phi implies $chi)\);
    infer is_formula(\(($psi implies $chi) implies ($phi implies $chi))\);
    infer is_formula(\(($phi implies $psi) implies
      (($psi implies $chi) implies ($phi implies $chi)))\);

    step hypothetical_syllogism(\$phi\, \$psi\, \$chi\);
    step implication_commutation(\($psi implies $chi)\, \($phi implies $psi)\,
      \($phi implies $chi)\);
    step modus_ponens(\(($psi implies $chi) implies
      (($phi implies $psi) implies ($phi implies $chi)))\,
      \(($phi implies $psi) implies
      (($psi implies $chi) implies ($phi implies $chi)))\);
  }

  theorem
  transposition_2(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(($phi implies $psi) implies
      (not $psi implies not $phi))\);
    infer is_formula(\($phi implies $psi)\);
    infer is_formula(\not $phi\);
    infer is_formula(\not $psi\);
    infer is_formula(\(not $psi implies not $phi)\);
    infer is_formula(\(($phi implies $psi) implies
      (not $psi implies not $phi))\);

    step double_negation_right(\$psi\);
    step hypothetical_syllogism(\$phi\, \$psi\, \not not $psi\);
    step modus_ponens(\($psi implies not not $psi)\,
      \(($phi implies $psi) implies ($phi implies not not $psi))\);
    step double_negation_left(\$phi\);
    step hypothetical_syllogism_2(\not not $phi\, \$phi\, \not not $psi\);
    step modus_ponens(\(not not $phi implies $phi)\,
      \(($phi implies not not $psi) implies
      (not not $phi implies not not $psi))\);
    step hypothetical_syllogism_meta(\($phi implies $psi)\,
      \($phi implies not not $psi)\,
      \(not not $phi implies not not $psi)\);
    step transposition(\not $psi\, \not $phi\);
    step hypothetical_syllogism_meta(\($phi implies $psi)\,
      \(not not $phi implies not not $psi)\,
      \(not $psi implies not $phi)\);
  }

  theorem
  modus_tollens(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume has_proof(\($phi implies $psi)\);
    assume has_proof(\not $psi\);

    infer has_proof(\not $phi\);

    step transposition_2(\$phi\, \$psi\);
    step modus_ponens(\($phi implies $psi)\, \(not $psi implies not $phi)\);
    step modus_ponens(\not $psi\, \not $phi\);
  }

  theorem
  transposition_3(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\((not $phi implies $psi)
      implies (not $psi implies $phi))\);

    step WF_negation(\$phi\);
    step transposition_2(\not $phi\, \$psi\);
    step double_negation_left(\$phi\);
    step hypothetical_syllogism(\not $psi\, \not not $phi\, \$phi\);
    step modus_ponens(\(not not $phi implies $phi)\,
      \((not $psi implies not not $phi) implies (not $psi implies $phi))\);
    step hypothetical_syllogism_meta(\(not $phi implies $psi)\,
      \(not $psi implies not not $phi)\,
      \(not $psi implies $phi)\);
  }

  theorem
  contradiction(phi)
  {
    assume is_formula(\$phi\);

    infer has_proof(\((not $phi implies $phi) implies $phi)\);

    step WF_negation(\$phi\);
    step WF_implication(\$phi\, \$phi\);
    step WF_negation(\($phi implies $phi)\);
    step WF_negation(\not ($phi implies $phi)\);
    step simplification(\not $phi\, \not not ($phi implies $phi)\);
    step transposition(\$phi\, \not ($phi implies $phi)\);
    step hypothetical_syllogism_meta(\not $phi\,
      \(not not ($phi implies $phi) implies not $phi)\,
      \($phi implies not ($phi implies $phi))\);
    step distributive(\not $phi\, \$phi\, \not ($phi implies $phi)\);
    step modus_ponens(\(not $phi implies
      ($phi implies not ($phi implies $phi)))\,
      \((not $phi implies $phi)
      implies (not $phi implies not ($phi implies $phi)))\);
    step transposition(\($phi implies $phi)\, \$phi\);
    step hypothetical_syllogism_meta(\(not $phi implies $phi)\,
      \(not $phi implies not ($phi implies $phi))\,
      \(($phi implies $phi) implies $phi)\);
    step identity(\$phi\);
    step double_simplification(\($phi implies $phi)\, \$phi\);
    step modus_ponens(\($phi implies $phi)\,
      \((($phi implies $phi) implies $phi) implies $phi)\);
    step hypothetical_syllogism_meta(\(not $phi implies $phi)\,
      \(($phi implies $phi) implies $phi)\,
      \$phi\);
  }

  /* Extend the system to include the other connectives we use and prove common
     theorems. */
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

/*
  theorem
  biconditional_to_implication(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(($phi iff $psi) implies ($phi implies $psi))\);
  }
*/

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
equality. Then prove utility theorems. We use the following definitions
from Mendelsonfor free, bound, and free for:

An occurrence of a variable x is said to be bound in a wf phi
if either it is the occurrence of x in a quantifier (any x) in phi or it
lies within the scope of a quantifier (any x) in phi.
Otherwise, the occurrence is said to be free in phi.

A variable is said to be free (bound) in a wf phi if it has a free (bound)
occurrence in phi.

If phi is a wf and t is a term, then t is said to be free for x in phi if
no free occurrence of x in phi lies within the scope of any quantifier
(any y), where y is a variable in t.

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
  WF_universal(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);

    infer is_formula(\any $x $phi\);
  }

  axiom
  _generalization(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);
    assume has_proof(\$phi\);

    infer has_proof(\any $x $phi\);
  }

  theorem
  generalization(x, phi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);
    assume has_proof(\$phi\);

    infer has_proof(\any $x $phi\);

    step _generalization(\$x\, \$phi\);
    step WF_universal(\$x\, \$phi\);
  }

  axiom
  _instantiation(x, t, phi)
  {
    assume is_variable(\$x\);
    assume is_term(\$t\);
    assume is_formula(\$phi\);
    assume free_for(\$x\, \$t\, \$phi\);

    infer has_proof(\any $x $phi implies $phi[x=\$t\]\);
  }

  axiom
  _quantified_implication(x, phi, psi)
  {
    assume is_variable(\$x\);
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);
    assume not_free_in(\$x\, \$phi\);

    infer has_proof(\(any $x ($phi implies $psi) implies
      ($phi implies any $x $psi))\);
  }

  axiom
  WF_equality(x, y)
  {
    assume is_term(\$x\);
    assume is_term(\$y\);

    infer is_formula(\$x = $y\);
  }

  axiom
  _eq_reflixive(x)
  {
    assume is_variable(\$x\);

    infer has_proof(\any $x $x = $x\);
  }

  axiom
  _eq_substitution(x, y, phi)
  {
    assume is_variable(\$x\);
    assume is_variable(\$y\);
    assume is_formula(\$phi\);
    assume free_for(\$x\, \$y\, \$phi\);

    infer has_proof(\($x = $y implies ($phi[x=\$x\] implies $phi[x=\$y\]))\);
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

    infer has_proof(\any $x any $y
      ($x subset $y iff any $z ($z in $x implies $z in $y))\);
  }

  axiom
  _variables()
  {
    infer is_variable(\_x\);
    infer is_variable(\_y\);
    infer is_variable(\_z\);
  }

  axiom
  TMP_biconditional_implication(phi, psi)
  {
    assume is_formula(\$phi\);
    assume is_formula(\$psi\);

    infer has_proof(\(($phi iff $psi) implies ($phi implies $psi))\);
  }

/*
  theorem
  subset_reflexive(x)
  {
    assume is_variable(\$x\);

    infer has_proof(\any $x $x subset $x\);

    step _variables();
    step variables_are_terms(\_z\);
    step variables_are_terms(\$x\);
    step WF_membership(\_z\, \$x\);
    step identity(\_z in $x\);
    step WF_implication(\_z in $x\, \_z in $x\);
    step generalization(\_z\, \(_z in $x implies _z in $x)\);
    step D_subset(\$x\, \$x\, \_z\);
    step WF_subset(\$x\, \$x\);
    step WF_biconditional(\$\, \\);
    step WF_implication();
  }
*/

/*
  theorem subset_transitive(x, y, z)
  {
    assume is_variable(\$x\);
    assume is_variable(\$y\);
    assume is_variable(\$z\);

    infer has_proof(\any $x any $y any $z (($x subset $y and $y subset $z) implies $x subset $z)\);
  }
*/

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
