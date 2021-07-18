/*

Propositional Calculus:

Postulate rules for forming formulas, using negation and implication. Then
add the axioms for propositional calculus. These are axioms P2, P3, and P4
as shown in:
  https://en.wikipedia.org/wiki/Hilbert_system.

Axiom P1 is proven as `identity`. We then extend our system to include the
connectives "if and only if", "or", and "and".

*/
namespace propositional_calculus
{
  type Formula;

  expr Formula
  implies(phi : Formula, psi : Formula);

  expr Formula
  not(phi : Formula);

  axiom
  modus_ponens(phi : Formula, psi : Formula)
  {
    assume $phi;
    assume implies($phi, $psi);

    infer $psi;
  }

  axiom simplification(phi : Formula, psi : Formula)
  {
    infer implies($phi, implies($psi, $phi));
  }

  axiom distributive(phi : Formula, psi : Formula, chi : Formula)
  {
    def A implies($phi, implies($psi, $chi));
    def B implies(implies($phi, $psi), implies($phi, $chi));

    infer implies(%A, %B);
  }

  axiom transposition(phi : Formula, psi : Formula)
  {
    infer implies(implies(not($psi), not($phi)), implies($phi, $psi));
  }

  const T : Formula;

  axiom
  true()
  {
    infer T;
  }

  const F : Formula;

  axiom
  false()
  {
    infer not(F);
  }

  /*

  Common theorems of propositional calculus, based on the list given in
  https://en.wikipedia.org/wiki/Hilbert_system

  */
  theorem
  identity(phi : Formula)
  {
    infer implies($phi, $phi);

    step simplification($phi, implies($phi, $phi));
    step distributive($phi, implies($phi, $phi), $phi);
    step modus_ponens(implies($phi, implies(implies($phi, $phi), $phi)),
      implies(implies($phi, implies($phi, $phi)), implies($phi, $phi)));
    step simplification($phi, $phi);
    step modus_ponens(implies($phi, implies($phi, $phi)), implies($phi, $phi));
  }

  theorem
  hypothetical_syllogism(phi : Formula, psi : Formula,
    chi : Formula)
  {
    infer implies(implies($psi, $chi),
      implies(implies($phi, $psi), implies($phi, $chi)));

    step distributive($phi, $psi, $chi);
    step simplification(implies(implies($phi, implies($psi, $chi)),
      implies(implies($phi, $psi), implies($phi, $chi))), implies($psi, $chi));
    step modus_ponens(implies(implies($phi, implies($psi, $chi)),
      implies(implies($phi, $psi), implies($phi, $chi))),
      implies(implies($psi, $chi), implies(implies($phi, implies($psi, $chi)),
      implies(implies($phi, $psi), implies($phi, $chi)))));
    step distributive(implies($psi, $chi), implies($phi, implies($psi, $chi)),
      implies(implies($phi, $psi), implies($phi, $chi)));
    step modus_ponens(implies(implies($psi, $chi), implies(implies($phi,
      implies($psi, $chi)), implies(implies($phi, $psi), implies($phi, $chi)))),
      implies(implies(implies($psi, $chi), implies($phi, implies($psi, $chi))),
      implies(implies($psi, $chi), implies(implies($phi, $psi),
      implies($phi, $chi)))));
    step simplification(implies($psi, $chi), $phi);
    step modus_ponens(implies(implies($psi, $chi),
      implies($phi, implies($psi, $chi))),
      implies(implies($psi, $chi), implies(implies($phi, $psi),
      implies($phi, $chi))));
  }

  theorem
  hypothetical_syllogism_meta(phi : Formula, psi : Formula,
    chi : Formula)
  {
    assume implies($psi, $chi);
    assume implies($phi, $psi);

    infer implies($phi, $chi);

    step hypothetical_syllogism($phi, $psi, $chi);
    step modus_ponens(implies($psi, $chi),
      implies(implies($phi, $psi), implies($phi, $chi)));
    step modus_ponens(implies($phi, $psi), implies($phi, $chi));
  }

  theorem
  double_simplification(phi : Formula, psi : Formula)
  {
    infer implies($phi, implies(implies($phi, $psi), $psi));

    step distributive(implies($phi, $psi), $phi, $psi);
    step identity(implies($phi, $psi));
    step modus_ponens(implies(implies($phi, $psi), implies($phi, $psi)),
      implies(implies(implies($phi, $psi), $phi),
      implies(implies($phi, $psi), $psi)));
    step hypothetical_syllogism($phi, implies(implies($phi, $psi), $phi),
      implies(implies($phi, $psi), $psi));
    step modus_ponens(implies(implies(implies($phi, $psi), $phi),
      implies(implies($phi, $psi), $psi)),
      implies(implies($phi, implies(implies($phi, $psi), $phi)),
      implies($phi, implies(implies($phi, $psi), $psi))));
    step simplification($phi, implies($phi, $psi));
    step modus_ponens(implies($phi, implies(implies($phi, $psi), $phi)),
      implies($phi, implies(implies($phi, $psi), $psi)));
  }

  theorem
  double_negation_left(phi : Formula)
  {
    infer implies(not(not($phi)), $phi);

    step true();
    step simplification($phi, $phi);
    step transposition(not($phi), not(T));
    step transposition(T, $phi);
    step hypothetical_syllogism_meta(implies(not(not(T)), not(not($phi))),
      implies(not($phi), not(T)), implies(T, $phi));
    step simplification(not(not($phi)), not(not(T)));
    step hypothetical_syllogism_meta(not(not($phi)),
      implies(not(not(T)), not(not($phi))), implies(T, $phi));
    step double_simplification(T, $phi);
    step modus_ponens(T, implies(implies(T, $phi), $phi));
    step hypothetical_syllogism_meta(not(not($phi)), implies(T, $phi),
      $phi);
  }

  theorem
  double_negation_right(phi : Formula)
  {
    infer implies($phi, not(not($phi)));

    step double_negation_left(not($phi));
    step transposition($phi, not(not($phi)));
    step modus_ponens(implies(not(not(not($phi))), not($phi)),
      implies($phi, not(not($phi))));
  }

  theorem
  implication_commutation(phi : Formula, psi : Formula, chi : Formula)
  {
    infer implies(implies($phi, implies($psi, $chi)),
      implies($psi, implies($phi, $chi)));

    step distributive($phi, $psi, $chi);
    step hypothetical_syllogism($psi, implies($phi, $psi), implies($phi, $chi));
    step hypothetical_syllogism_meta(implies($phi, implies($psi, $chi)),
      implies(implies($phi, $psi), implies($phi, $chi)),
      implies(implies($psi, implies($phi, $psi)),
      implies($psi, implies($phi, $chi))));
    step distributive(implies($phi, implies($psi, $chi)),
      implies($psi, implies($phi, $psi)),
      implies($psi, implies($phi, $chi)));
    step modus_ponens(implies(implies($phi, implies($psi, $chi)),
      implies(implies($psi, implies($phi, $psi)),
      implies($psi, implies($phi, $chi)))),
      implies(implies(implies($phi, implies($psi, $chi)),
      implies($psi, implies($phi, $psi))), implies(implies($phi,
      implies($psi, $chi)), implies($psi, implies($phi, $chi)))));
    step simplification($psi, $phi);
    step simplification(implies($psi, implies($phi, $psi)),
      implies($phi, implies($psi, $chi)));
    step modus_ponens(implies($psi, implies($phi, $psi)),
      implies(implies($phi, implies($psi, $chi)),
      implies($psi, implies($phi, $psi))));
    step modus_ponens(implies(implies($phi, implies($psi, $chi)),
      implies($psi, implies($phi, $psi))),
      implies(implies($phi, implies($psi, $chi)),
      implies($psi, implies($phi, $chi))));
  }

  theorem
  hypothetical_syllogism_2(phi : Formula, psi : Formula, chi : Formula)
  {
    infer implies(implies($phi, $psi),
      implies(implies($psi, $chi), implies($phi, $chi)));

    step hypothetical_syllogism($phi, $psi, $chi);
    step implication_commutation(implies($psi, $chi), implies($phi, $psi),
      implies($phi, $chi));
    step modus_ponens(implies(implies($psi, $chi),
      implies(implies($phi, $psi), implies($phi, $chi))),
      implies(implies($phi, $psi),
      implies(implies($psi, $chi), implies($phi, $chi))));
  }

  theorem
  transposition_2(phi : Formula, psi : Formula)
  {
    infer implies(implies($phi, $psi), implies(not($psi), not($phi)));

    step double_negation_right($psi);
    step hypothetical_syllogism($phi, $psi, not(not($psi)));
    step modus_ponens(implies($psi, not(not($psi))),
      implies(implies($phi, $psi), implies($phi, not(not($psi)))));
    step double_negation_left($phi);
    step hypothetical_syllogism_2(not(not($phi)), $phi, not(not($psi)));
    step modus_ponens(implies(not(not($phi)), $phi),
      implies(implies($phi, not(not($psi))),
      implies(not(not($phi)), not(not($psi)))));
    step hypothetical_syllogism_meta(implies($phi, $psi),
      implies($phi, not(not($psi))),
      implies(not(not($phi)), not(not($psi))));
    step transposition(not($psi), not($phi));
    step hypothetical_syllogism_meta(implies($phi, $psi),
      implies(not(not($phi)), not(not($psi))),
      implies(not($psi), not($phi)));
  }

  theorem
  modus_tollens(phi : Formula, psi : Formula)
  {
    assume implies($phi, $psi);
    assume not($psi);

    infer not($phi);

    step transposition_2($phi, $psi);
    step modus_ponens(implies($phi, $psi), implies(not($psi), not($phi)));
    step modus_ponens(not($psi), not($phi));
  }

  theorem
  transposition_3(phi : Formula, psi : Formula)
  {
    infer implies(implies(not($phi), $psi), implies(not($psi), $phi));

    step transposition_2(not($phi), $psi);
    step double_negation_left($phi);
    step hypothetical_syllogism(not($psi), not(not($phi)), $phi);
    step modus_ponens(implies(not(not($phi)), $phi),
      implies(implies(not($psi), not(not($phi))), implies(not($psi), $phi)));
    step hypothetical_syllogism_meta(implies(not($phi), $psi),
      implies(not($psi), not(not($phi))),
      implies(not($psi), $phi));
  }

  theorem
  contradiction(phi : Formula)
  {
    infer implies(implies(not($phi), $phi), $phi);

    step simplification(not($phi), not(not(implies($phi, $phi))));
    step transposition($phi, not(implies($phi, $phi)));
    step hypothetical_syllogism_meta(not($phi),
      implies(not(not(implies($phi, $phi))), not($phi)),
      implies($phi, not(implies($phi, $phi))));
    step distributive(not($phi), $phi, not(implies($phi, $phi)));
    step modus_ponens(implies(not($phi), implies($phi,
      not(implies($phi, $phi)))), implies(implies(not($phi), $phi),
      implies(not($phi), not(implies($phi, $phi)))));
    step transposition(implies($phi, $phi), $phi);
    step hypothetical_syllogism_meta(implies(not($phi), $phi),
      implies(not($phi), not(implies($phi, $phi))),
      implies(implies($phi, $phi), $phi));
    step identity($phi);
    step double_simplification(implies($phi, $phi), $phi);
    step modus_ponens(implies($phi, $phi),
      implies(implies(implies($phi, $phi), $phi), $phi));
    step hypothetical_syllogism_meta(implies(not($phi), $phi),
      implies(implies($phi, $phi), $phi), $phi);
  }

  theorem
  intermediate_elimination(phi : Formula, psi : Formula, chi : Formula)
  {
    assume implies($phi, implies($psi, $chi));
    assume $psi;

    infer implies($phi, $chi);

    step distributive($phi, $psi, $chi);
    step modus_ponens(implies($phi, implies($psi, $chi)),
      implies(implies($phi, $psi), implies($phi, $chi)));
    step simplification($psi, $phi);
    step modus_ponens($psi, implies($phi, $psi));
    step modus_ponens(implies($phi, $psi), implies($phi, $chi));
  }

  /* Extend the system to include the other connectives we use and prove common
     theorems. */
  /* TODO: Instead of explicitly adding these connectives and their properties
     as axioms, add them as extension by definition and prove these properties
     as theorems. */
  expr Formula
  and(phi : Formula, psi : Formula);

  axiom
  conjunction_introduction(phi : Formula, psi : Formula)
  {
    infer implies($phi, implies($psi, and($phi, $psi)));
  }

  theorem
  conjunction_introduction_meta(phi : Formula, psi : Formula)
  {
    assume $phi;
    assume $psi;

    infer and($phi, $psi);

    step conjunction_introduction($phi, $psi);
    step modus_ponens($phi, implies($psi, and($phi, $psi)));
    step modus_ponens($psi, and($phi, $psi));
  }

  axiom
  conjunction_elimination_left(phi : Formula, psi : Formula)
  {
    infer implies(and($phi, $psi), $phi);
  }

  theorem
  conjunction_elimination_left_meta(phi : Formula, psi : Formula)
  {
    assume and($phi, $psi);

    infer $phi;

    step conjunction_elimination_left($phi, $psi);
    step modus_ponens(and($phi, $psi), $phi);
  }

  axiom
  conjunction_elimination_right(phi : Formula, psi : Formula)
  {
    infer implies(and($phi, $psi), $psi);
  }

  theorem
  conjunction_elimination_right_meta(phi : Formula, psi : Formula)
  {
    assume and($phi, $psi);

    infer $psi;

    step conjunction_elimination_right($phi, $psi);
    step modus_ponens(and($phi, $psi), $psi);
  }

  theorem
  conjunction_elimination_meta(phi : Formula, psi : Formula)
  {
    assume and($phi, $psi);

    infer $phi;
    infer $psi;

    step conjunction_elimination_left_meta($phi, $psi);
    step conjunction_elimination_right_meta($phi, $psi);
  }

  expr Formula
  or(phi : Formula, psi : Formula);

  axiom
  disjunction_introduction_left(phi : Formula, psi : Formula)
  {
    infer implies($phi, or($phi, $psi));
  }

  theorem
  disjunction_introduction_left_meta(phi : Formula, psi : Formula)
  {
    assume $phi;

    infer or($phi, $psi);

    step disjunction_introduction_left($phi, $psi);
    step modus_ponens($phi, or($phi, $psi));
  }

  axiom
  disjunction_introduction_right(phi : Formula, psi : Formula)
  {
    infer implies($psi, or($phi, $psi));
  }

  theorem
  disjunction_introduction_right_meta(phi : Formula, psi : Formula)
  {
    assume $psi;

    infer or($phi, $psi);

    step disjunction_introduction_right($phi, $psi);
    step modus_ponens($psi, or($phi, $psi));
  }

  axiom
  disjunction_elimination(phi : Formula, psi : Formula, chi : Formula)
  {
    infer implies(implies(implies($phi, $chi), implies($psi, $chi)),
      implies(or($phi, $psi), $chi));
  }

  theorem
  disjunction_elimination_meta(phi : Formula, psi : Formula, chi : Formula)
  {
    assume implies($phi, $chi);
    assume implies($psi, $chi);
    assume or($phi, $psi);

    infer $chi;

    step disjunction_elimination($phi, $psi, $chi);
    step simplification(implies($psi, $chi), implies($phi, $chi));
    step modus_ponens(implies($psi, $chi),
      implies(implies($phi, $chi), implies($psi, $chi)));
    step modus_ponens(implies(implies($phi, $chi), implies($psi, $chi)),
      implies(or($phi, $psi), $chi));
    step modus_ponens(or($phi, $psi), $chi);
  }

  expr Formula
  iff(phi : Formula, psi : Formula);

  axiom
  biconditional_introduction(phi : Formula, psi : Formula)
  {
    infer implies(and(implies($phi, $psi), implies($psi, $phi)),
      iff($phi, $psi));
  }

  theorem
  biconditional_introduction_meta(phi : Formula, psi : Formula)
  {
    assume implies($phi, $psi);
    assume implies($psi, $phi);

    infer iff($phi, $psi);

    step conjunction_introduction_meta(implies($phi, $psi),
      implies($psi, $phi));
    step biconditional_introduction($phi, $psi);
    step modus_ponens(and(implies($phi, $psi), implies($psi, $phi)),
      iff($phi, $psi));
  }

  axiom
  biconditional_elimination_left(phi : Formula, psi : Formula)
  {
    infer implies(iff($phi, $psi), implies($psi, $phi));
  }

  theorem
  biconditional_elimination_left_meta(phi : Formula, psi : Formula)
  {
    assume iff($phi, $psi);

    infer implies($psi, $phi);

    step biconditional_elimination_left($phi, $psi);
    step modus_ponens(iff($phi, $psi), implies($psi, $phi));
  }

  axiom
  biconditional_elimination_right(phi : Formula, psi : Formula)
  {
    infer implies(iff($phi, $psi), implies($phi, $psi));
  }

  theorem
  biconditional_elimination_right_meta(phi : Formula, psi : Formula)
  {
    assume iff($phi, $psi);

    infer implies($phi, $psi);

    step biconditional_elimination_right($phi, $psi);
    step modus_ponens(iff($phi, $psi), implies($phi, $psi));
  }

  theorem
  biconditional_elimination_meta(phi : Formula, psi : Formula)
  {
    assume iff($phi, $psi);

    infer implies($psi, $phi);
    infer implies($phi, $psi);

    step biconditional_elimination_left_meta($phi, $psi);
    step biconditional_elimination_right_meta($phi, $psi);
  }
}
/* alias propositional_calculus prop; */

/*

First Order Logic (with Equality):

Define terms, variables, and quantification. After developing the rules
for free and bound variables, add the axioms for first order logic with
equality. The axioms are taken from Mendelson, pgs. 69-70 and 95.

*/
namespace predicate_calculus
{
  use propositional_calculus;

  type Term;
  type Variable atomic;
  type Function atomic;
  type Predicate2 atomic;

  namespace vars
  {
    const x : Variable;
    const y : Variable;
    const z : Variable;

    const a : Variable;
    const b : Variable;
    const c : Variable;

    const n : Variable;
  }

  expr Term
  t(x : Variable);

  expr Term
  eval_f(f : Function, t : Term);

  expr Formula
  eval_p(p : Predicate2, s : Term, t : Term);

  expr Formula
  any(x : Variable, phi : Formula) binds ($x);

  axiom
  instantiation(x : Variable, phi : Formula, t : Term, phi0 : Formula)
  {
    require free_for($t, t($x), $phi);
    require full_substitution(t($x), $phi, $t, $phi0);

    infer implies(any($x, $phi), $phi0);
  }

  axiom
  universal_elimination(x : Variable, phi : Formula, psi : Formula)
  {
    require not_free($x, $phi);

    infer implies(any($x, implies($phi, $psi)),
      implies($phi, any($x, $psi)));
  }

  axiom
  generalization(x : Variable, phi : Formula)
  {
    assume $phi;

    infer any($x, $phi);
  }

  theorem
  instantiation_elimination(x : Variable, phi : Formula)
  {
    infer implies(any($x, $phi), $phi);

    step instantiation($x, $phi, t($x), $phi);
  }

  expr Formula
  eq(s : Term, y : Term);

  axiom
  equality_reflexive_v(x : Variable)
  {
    infer any($x, eq(t($x), t($x)));
  }

  axiom
  equality_substitution(x : Variable, phi : Formula, y : Variable,
    phi0 : Formula)
  {
    require free_for(t($y), t($x), $phi);
    require substitution(t($x), $phi, t($y), $phi0);

    infer implies(eq(t($x), t($y)), implies($phi, $phi0));
  }

  /*theorem
  equality_symmetric(x : Variable, y : Variable)
  {
    infer any($x, any($y, iff(eq(t($x), t($y)), eq(t($y), t($x)))));

    step equality_substitution($x, eq(t($x), t($x)),
      $y, eq(t($y), t($x)));
  }*/
}
/* alias predicate_calculus pred; */

namespace zfc
{
  use propositional_calculus;
  use predicate_calculus;

  const in : Predicate2;

  axiom
  extensionality()
  {
    infer any(vars.x, any(vars.y, implies(
      any(vars.z, iff(eval_p(in, t(vars.z), t(vars.x)),
      eval_p(in, t(vars.z), t(vars.y)))), eq(t(vars.x), t(vars.y)))));
  }
}
