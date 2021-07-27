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
  implies(phi : Formula, psi : Formula)
  {
    latex "\\left( " + $phi + " \\implies " + $psi + " \\right)";
  }

  expr Formula
  not(phi : Formula)
  {
    latex "\\neg " + $phi;
  }

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

  const T : Formula
  {
    latex "\\top";
  }

  axiom
  true()
  {
    infer T;
  }

  const F : Formula
  {
    latex "\\bot";
  }

  axiom
  false()
  {
    infer not(F);
  }

  /*

  Some of my own common theorems.

  */
  theorem
  false_implies(phi : Formula)
  {
    infer implies(F, $phi);

    step transposition(F, $phi);
    step simplification(not(F), not($phi));
    step false();
    step modus_ponens(not(F), implies(not($phi), not(F)));
    step modus_ponens(implies(not($phi), not(F)), implies(F, $phi));
  }

  theorem
  implies_true_formula(phi : Formula, psi : Formula)
  {
    assume $psi;

    infer implies($phi, $psi);

    step simplification($psi, $phi);
    step modus_ponens($psi, implies($phi, $psi));
  }

  theorem
  implies_true(phi : Formula)
  {
    infer implies($phi, T);

    step true();
    step implies_true_formula($phi, T);
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

  /* Some more common theorems. */
  /* TODO: prove this as a tautology first? */
  theorem
  triple_antecedent_introduction_meta(phi : Formula, psi : Formula,
    chi : Formula, theta : Formula)
  {
    assume implies($phi, implies($psi, $chi));

    infer implies(implies($theta, $phi),
      implies(implies($theta, $psi), implies($theta, $chi)));

    step hypothetical_syllogism($theta, $phi, implies($psi, $chi));
    step modus_ponens(implies($phi, implies($psi, $chi)),
      implies(implies($theta, $phi), implies($theta, implies($psi, $chi))));
    step distributive($theta, $psi, $chi);
    step hypothetical_syllogism_meta(implies($theta, $phi),
      implies($theta, implies($psi, $chi)),
      implies(implies($theta, $psi), implies($theta, $chi)));
  }

  /* Extend the system to include the other connectives we use and prove common
     theorems. */
  /* TODO: Instead of explicitly adding these connectives and their properties
     as axioms, add them as extension by definition and prove these properties
     as theorems. */
  expr Formula
  and(phi : Formula, psi : Formula)
  {
    latex "\\left( " + $phi + " \\land " + $psi + " \\right)";
  }

  axiom
  conjunction_introduction(phi : Formula, psi : Formula)
  {
    infer implies($phi, implies($psi, and($phi, $psi)));
  }

  theorem
  hypothetical_conjunction_introduction(phi : Formula,
    psi : Formula, chi : Formula)
  {
    infer implies(implies($phi, $psi), implies(implies($phi, $chi),
      implies($phi, and($psi, $chi))));

    step conjunction_introduction($psi, $chi);
    step triple_antecedent_introduction_meta($psi, $chi, and($psi, $chi), $phi);
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

  theorem
  negative_conjunction_introduction(phi : Formula, psi : Formula)
  {
    infer implies(not($phi), not(and($psi, $phi)));

    step conjunction_elimination_right($psi, $phi);
    step transposition_2(and($psi, $phi), $phi);
    step modus_ponens(implies(and($psi, $phi), $phi),
      implies(not($phi), not(and($psi, $phi))));
  }

  theorem
  conjunction_implication_distributive(phi : Formula, psi : Formula,
    chi : Formula)
  {
    infer implies(and(implies($phi, $psi), implies($phi, $chi)),
      implies($phi, and($psi, $chi)));

    step hypothetical_conjunction_introduction($phi, $psi, $chi);
    step conjunction_elimination_left(implies($phi, $psi),
      implies($phi, $chi));
    step conjunction_elimination_right(implies($phi, $psi),
      implies($phi, $chi));
    step hypothetical_syllogism_meta(and(implies($phi, $psi),
      implies($phi, $chi)), implies($phi, $psi),
      implies(implies($phi, $chi), implies($phi, and($psi, $chi))));
    step distributive(and(implies($phi, $psi), implies($phi, $chi)),
      implies($phi, $chi), implies($phi, and($psi, $chi)));
    step modus_ponens(implies(and(implies($phi, $psi), implies($phi, $chi)),
      implies(implies($phi, $chi), implies($phi, and($psi, $chi)))),
      implies(implies(and(implies($phi, $psi), implies($phi, $chi)),
      implies($phi, $chi)), implies(and(implies($phi, $psi),
      implies($phi, $chi)), implies($phi, and($psi, $chi)))));
    step modus_ponens(implies(and(implies($phi, $psi), implies($phi, $chi)),
      implies($phi, $chi)), implies(and(implies($phi, $psi),
      implies($phi, $chi)), implies($phi, and($psi, $chi))));
  }

  expr Formula
  or(phi : Formula, psi : Formula)
  {
    latex "\\left( " + $phi + " \\lor " + $psi + " \\right)";
  }

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
  iff(phi : Formula, psi : Formula)
  {
    latex "\\left( " + $phi + " \\iff " + $psi + " \\right)";
  }

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

  theorem
  biconditional_distribution_left(phi : Formula, psi : Formula, chi : Formula)
  {
    infer implies(iff($phi, $psi),
      implies(implies($phi, $chi), implies($psi, $chi)));

    step biconditional_elimination_left($phi, $psi);
    step hypothetical_syllogism_2($psi, $phi, $chi);
    step hypothetical_syllogism_meta(iff($phi, $psi), implies($psi, $phi),
      implies(implies($phi, $chi), implies($psi, $chi)));
  }

  theorem
  biconditional_distribution_right(phi : Formula, psi : Formula, chi : Formula)
  {
    infer implies(iff($phi, $psi),
      implies(implies($chi, $phi), implies($chi, $psi)));

    step biconditional_elimination_right($phi, $psi);
    step hypothetical_syllogism($chi, $phi, $psi);
    step hypothetical_syllogism_meta(iff($phi, $psi), implies($phi, $psi),
      implies(implies($chi, $phi), implies($chi, $psi)));
  }

  theorem
  infer_negated_equivalent(phi : Formula, psi : Formula, chi : Formula)
  {
    assume not($chi);
    assume implies($phi, iff($psi, $chi));

    infer implies($phi, not($psi));

    step biconditional_elimination_right($psi, $chi);
    step hypothetical_syllogism_meta($phi, iff($psi, $chi),
      implies($psi, $chi));
    step transposition_2($psi, $chi);
    step hypothetical_syllogism_meta($phi, implies($psi, $chi),
      implies(not($chi), not($psi)));
    step intermediate_elimination($phi, not($chi), not($psi));
  }

  namespace lemma
  {
    /*
    theorem
    biconditional_introduction_from_implication(phi : Formula, psi : Formula)
    {
      infer implies(implies($phi, $psi), implies(implies($psi, $phi),
        iff($phi, $psi)));

      step conjunction_introduction(implies($phi, $psi), implies($psi, $phi));
      step biconditional_introduction($phi, $psi);

    }
    */

    /*
    theorem
    biconditional_commutation_l1(phi : Formula, psi : Formula)
    {
      infer implies(iff($phi, $psi), iff($psi, $phi));

      step biconditional_elimination_left($phi, $psi);
      step biconditional_elimination_right($phi, $psi);
      step biconditional_introduction($psi, $phi);
      step conjunction_introduction(implies($psi, $phi), implies($phi, $psi));
      step hypothetical_syllogism_meta()
    }
    */
  }

  namespace lemma
  {
    theorem
    conjunction_commutation_l1(phi : Formula, psi : Formula)
    {
      infer implies(and($phi, $psi), and($psi, $phi));

      step conjunction_elimination_left($phi, $psi);
      step conjunction_elimination_right($phi, $psi);
      step conjunction_introduction($psi, $phi);
      step hypothetical_syllogism_meta(and($phi, $psi), $psi,
        implies($phi, and($psi, $phi)));
      step distributive(and($phi, $psi), $phi, and($psi, $phi));
      step modus_ponens(implies(and($phi, $psi),
        implies($phi, and($psi, $phi))),
        implies(implies(and($phi, $psi), $phi),
        implies(and($phi, $psi), and($psi, $phi))));
      step modus_ponens(implies(and($phi, $psi), $phi),
        implies(and($phi, $psi), and($psi, $phi)));
    }
  }

  theorem
  conjunction_commutation(phi : Formula, psi : Formula)
  {
    infer iff(and($phi, $psi), and($psi, $phi));

    step lemma.conjunction_commutation_l1($phi, $psi);
    step lemma.conjunction_commutation_l1($psi, $phi);
    step biconditional_introduction_meta(and($phi, $psi), and($psi, $phi));
  }

  namespace lemma
  {
    theorem
    conjunction_biconditional_elimination_l1(phi : Formula, psi : Formula,
      chi : Formula)
    {
      infer implies(and(iff($psi, $phi), iff($chi, $phi)), implies($psi, $chi));

      step conjunction_elimination_left(iff($psi, $phi), iff($chi, $phi));
      step conjunction_elimination_right(iff($psi, $phi), iff($chi, $phi));
      step biconditional_elimination_right($psi, $phi);
      step biconditional_elimination_left($chi, $phi);
      step hypothetical_syllogism_meta(and(iff($psi, $phi), iff($chi, $phi)),
        iff($psi, $phi), implies($psi, $phi));
      step hypothetical_syllogism_meta(and(iff($psi, $phi), iff($chi, $phi)),
        iff($chi, $phi), implies($phi, $chi));
      step hypothetical_syllogism_2($psi, $phi, $chi);
      step hypothetical_syllogism_meta(and(iff($psi, $phi), iff($chi, $phi)),
        implies($psi, $phi), implies(implies($phi, $chi), implies($psi, $chi)));
      step distributive(and(iff($psi, $phi), iff($chi, $phi)),
        implies($phi, $chi), implies($psi, $chi));
      step modus_ponens(implies(and(iff($psi, $phi), iff($chi, $phi)),
        implies(implies($phi, $chi), implies($psi, $chi))),
        implies(implies(and(iff($psi, $phi), iff($chi, $phi)),
        implies($phi, $chi)), implies(and(iff($psi, $phi), iff($chi, $phi)),
        implies($psi, $chi))));
      step modus_ponens(implies(and(iff($psi, $phi), iff($chi, $phi)),
        implies($phi, $chi)),
        implies(and(iff($psi, $phi), iff($chi, $phi)), implies($psi, $chi)));
    }
  }

/*
  theorem
  conjunction_biconditional_elimination(phi : Formula, psi : Formula,
    chi : formula)
  {
    infer implies(and(iff($psi, $phi), iff($chi, $phi)), iff($psi, $chi));

    step conjunction_biconditional_elimination_l1($phi, $psi, $chi);
    step conjunction_biconditional_elimination_l1($phi, $chi, $psi);
    step conjunction_commutation_l1(iff($chi, $phi), iff($psi, $phi));
    step hypothetical_syllogism_meta(and(iff($psi, $phi), iff($chi, $phi)),
      and(iff($chi, $phi), iff($psi, $phi)), implies($chi, $psi));
  }
*/

  theorem
  double_negation(phi : Formula)
  {
    infer iff($phi, not(not($phi)));

    step double_negation_left($phi);
    step double_negation_right($phi);
    step biconditional_introduction_meta($phi, not(not($phi)));
  }

  theorem
  false_conjunction(phi : Formula)
  {
    infer iff(and($phi, F), F);

    step conjunction_elimination_right($phi, F);
    step false_implies(and($phi, F));
    step biconditional_introduction_meta(and($phi, F), F);
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
  type Variable atomic binds;

  namespace vars
  {
    const a : Variable;
    const b : Variable;
    const c : Variable;
    const d : Variable;
    const e : Variable;
    const f : Variable;
    const g : Variable;
    const h : Variable;
    const i : Variable;
    const j : Variable;
    const k : Variable;
    const l : Variable;
    const m : Variable;
    const n : Variable;
    const o : Variable;
    const p : Variable;
    const q : Variable;
    const r : Variable;
    const s : Variable;
    const t : Variable;
    const u : Variable;
    const v : Variable;
    const w : Variable;
    const x : Variable;
    const y : Variable;
    const z : Variable;

    const A : Variable;
    const B : Variable;
    const C : Variable;
    const D : Variable;
    const E : Variable;
    const F : Variable;
    const G : Variable;
    const H : Variable;
    const I : Variable;
    const J : Variable;
    const K : Variable;
    const L : Variable;
    const M : Variable;
    const N : Variable;
    const O : Variable;
    const P : Variable;
    const Q : Variable;
    const R : Variable;
    const S : Variable;
    const T : Variable;
    const U : Variable;
    const V : Variable;
    const W : Variable;
    const X : Variable;
    const Y : Variable;
    const Z : Variable;
  }

  expr Term
  t(x : Variable)
  {
    latex $x;
  }

  expr Formula
  any(x : Variable, phi : Formula)
  {
    latex "\\forall " + $x + " " + $phi;
    bind $x;
  }

  axiom
  instantiation(x : Variable, phi : Formula, t : Term, phi_0 : Formula)
  {
    require free_for($t, t($x), $phi);
    require full_substitution(t($x), $phi, $t, $phi_0);

    infer implies(any($x, $phi), $phi_0);
  }

  axiom
  quantified_implication(x : Variable, phi : Formula, psi : Formula)
  {
    infer implies(any($x, implies($phi, $psi)),
      implies(any($x, $phi), any($x, $psi)));
  }

  axiom
  bound_generalization(x : Variable, phi : Formula)
  {
    require not_free($x, $phi);

    infer implies($phi, any($x, $phi));
  }

  axiom
  generalization(x : Variable, phi : Formula)
  {
    assume $phi;

    infer any($x, $phi);
  }

  theorem
  quantified_implication_meta(x : Variable, phi : Formula, psi : Formula)
  {
    assume implies($phi, $psi);

    infer implies(any($x, $phi), any($x, $psi));

    step generalization($x, implies($phi, $psi));
    step quantified_implication($x, $phi, $psi);
    step modus_ponens(any($x, implies($phi, $psi)),
      implies(any($x, $phi), any($x, $psi)));
  }

  theorem
  instantiation_elimination(x : Variable, phi : Formula)
  {
    infer implies(any($x, $phi), $phi);

    step instantiation($x, $phi, t($x), $phi);
  }

  theorem
  instantiation_elimination_meta(x : Variable, phi : Formula)
  {
    assume any($x, $phi);

    infer $phi;

    step instantiation_elimination($x, $phi);
    step modus_ponens(any($x, $phi), $phi);
  }

  theorem
  implication_generalization(x : Variable, phi : Formula, psi : Formula)
  {
    assume implies($phi, $psi);

    infer implies(any($x, $phi), any($x, $psi));

    step generalization($x, implies($phi, $psi));
    step quantified_implication($x, $phi, $psi);
    step modus_ponens(any($x, implies($phi, $psi)),
      implies(any($x, $phi), any($x, $psi)));
  }

  theorem
  quantified_conjunction(x : Variable, phi : Formula,
    psi : Formula)
  {
    infer implies(and(any($x, $phi), any($x, $psi)), any($x, and($phi, $psi)));

    step conjunction_elimination_left(any($x, $phi), any($x, $psi));
    step conjunction_elimination_right(any($x, $phi), any($x, $psi));
    step instantiation_elimination($x, $phi);
    step instantiation_elimination($x, $psi);
    step hypothetical_syllogism_meta(and(any($x, $phi), any($x, $psi)),
      any($x, $phi), $phi);
    step hypothetical_syllogism_meta(and(any($x, $phi), any($x, $psi)),
      any($x, $psi), $psi);
    step hypothetical_conjunction_introduction(and(any($x, $phi),
      any($x, $psi)), $phi, $psi);
    step modus_ponens(implies(and(any($x, $phi), any($x, $psi)), $phi),
      implies(implies(and(any($x, $phi), any($x, $psi)), $psi),
      implies(and(any($x, $phi), any($x, $psi)), and($phi, $psi))));
    step modus_ponens(implies(and(any($x, $phi), any($x, $psi)), $psi),
      implies(and(any($x, $phi), any($x, $psi)), and($phi, $psi)));
    step quantified_implication_meta($x, and(any($x, $phi), any($x, $psi)),
      and($phi, $psi));
    step bound_generalization($x, and(any($x, $phi), any($x, $psi)));
    step hypothetical_syllogism_meta(and(any($x, $phi), any($x, $psi)),
      any($x, and(any($x, $phi), any($x, $psi))),
      any($x, and($phi, $psi)));
  }

  /* TODO: prove this as a tautology (quantifying over the antecedent
     as well, or, equivalently, requiring the x not free in
     the antecedent). */
  theorem
  quantified_conjunction_implication_meta(x : Variable, phi : Formula,
    psi : Formula, chi : Formula)
  {
    assume implies(and($phi, $psi), $chi);

    infer implies(and(any($x, $phi), any($x, $psi)), any($x, $chi));

    step quantified_implication_meta($x, and($phi, $psi), $chi);
    step quantified_conjunction($x, $phi, $psi);
    step hypothetical_syllogism_meta(and(any($x, $phi), any($x, $psi)),
      any($x, and($phi, $psi)), any($x, $chi));
  }

  expr Formula
  eq(s : Term, t : Term)
  {
    latex $s + " = " + $t;
  }

  axiom
  equality_reflexive_v(x : Variable)
  {
    infer any($x, eq(t($x), t($x)));
  }

  axiom
  equality_substitution(x : Variable, phi : Formula, y : Variable,
    phi_0 : Formula)
  {
    require free_for(t($y), t($x), $phi);
    require substitution(t($x), $phi, t($y), $phi_0);

    infer implies(eq(t($x), t($y)), implies($phi, $phi_0));
  }

  theorem
  _equality_symmetric(x : Variable, y : Variable)
  {
    infer implies(eq(t($x), t($y)), eq(t($y), t($x)));

    step equality_reflexive_v($x);
    step instantiation_elimination($x, eq(t($x), t($x)));
    step modus_ponens(any($x, eq(t($x), t($x))), eq(t($x), t($x)));
    step equality_substitution($x, eq(t($x), t($x)), $y, eq(t($y), t($x)));
    step intermediate_elimination(eq(t($x), t($y)),
      eq(t($x), t($x)), eq(t($y), t($x)));
  }

  theorem
  equality_symmetric()
  {
    infer any(vars.x, any(vars.y,
      iff(eq(t(vars.x), t(vars.y)), eq(t(vars.y), t(vars.x)))));

    step _equality_symmetric(vars.x, vars.y);
    step _equality_symmetric(vars.y, vars.x);
    step biconditional_introduction_meta(eq(t(vars.x), t(vars.y)),
      eq(t(vars.y), t(vars.x)));
    step generalization(vars.y,
      iff(eq(t(vars.x), t(vars.y)), eq(t(vars.y), t(vars.x))));
    step generalization(vars.x, any(vars.y,
      iff(eq(t(vars.x), t(vars.y)), eq(t(vars.y), t(vars.x)))));
  }

  theorem
  equality_transitive()
  {
    def transitive implies(eq(t(vars.x), t(vars.y)), implies(eq(t(vars.y), t(vars.z)),
    eq(t(vars.x), t(vars.z))));

    infer any(vars.x, any(vars.y, any(vars.z,
      implies(eq(t(vars.x), t(vars.y)), implies(eq(t(vars.y), t(vars.z)),
      eq(t(vars.x), t(vars.z)))))));

    step equality_symmetric();
    step instantiation_elimination(vars.x, any(vars.y,
      iff(eq(t(vars.x), t(vars.y)), eq(t(vars.y), t(vars.x)))));
    step modus_ponens(any(vars.x, any(vars.y,
      iff(eq(t(vars.x), t(vars.y)), eq(t(vars.y), t(vars.x))))),
      any(vars.y, iff(eq(t(vars.x), t(vars.y)), eq(t(vars.y), t(vars.x)))));
    step instantiation_elimination(vars.y,
      iff(eq(t(vars.x), t(vars.y)), eq(t(vars.y), t(vars.x))));
    step modus_ponens(any(vars.y, iff(eq(t(vars.x), t(vars.y)),
      eq(t(vars.y), t(vars.x)))),
      iff(eq(t(vars.x), t(vars.y)), eq(t(vars.y), t(vars.x))));
    step equality_substitution(vars.y, eq(t(vars.y), t(vars.z)),
      vars.x, eq(t(vars.x), t(vars.z)));
    step biconditional_elimination_right_meta(eq(t(vars.x), t(vars.y)),
      eq(t(vars.y), t(vars.x)));
    step hypothetical_syllogism_meta(eq(t(vars.x), t(vars.y)),
      eq(t(vars.y), t(vars.x)),
      implies(eq(t(vars.y), t(vars.z)), eq(t(vars.x), t(vars.z))));
    step generalization(vars.z, %transitive);
    step generalization(vars.y, any(vars.z, %transitive));
    step generalization(vars.x, any(vars.y, any(vars.z, %transitive)));
  }

  expr Formula
  exists(x : Variable, phi : Formula)
  {
    latex "\\exists " + $x + " " + $phi;
    bind $x;
  }

  axiom
  existential_quantification(x : Variable, phi : Formula)
  {
    infer iff(exists($x, $phi), not(any($x, not($phi))));
  }

  theorem
  implication_generalization_existential(x : Variable, phi : Formula,
    psi : Formula)
  {
    assume implies($phi, $psi);

    infer implies(exists($x, $phi), exists($x, $psi));

    step transposition_2($phi, $psi);
    step modus_ponens(implies($phi, $psi), implies(not($psi), not($phi)));
    step implication_generalization($x, not($psi), not($phi));
    step transposition_2(any($x, not($psi)), any($x, not($phi)));
    step modus_ponens(implies(any($x, not($psi)), any($x, not($phi))),
      implies(not(any($x, not($phi))), not(any($x, not($psi)))));
    step existential_quantification($x, $phi);
    step biconditional_elimination_right_meta(exists($x, $phi),
      not(any($x, not($phi))));
    step hypothetical_syllogism_meta(exists($x, $phi),
      not(any($x, not($phi))), not(any($x, not($psi))));
    step existential_quantification($x, $psi);
    step biconditional_elimination_left_meta(exists($x, $psi),
      not(any($x, not($psi))));
    step hypothetical_syllogism_meta(exists($x, $phi),
      not(any($x, not($psi))), exists($x, $psi));
  }

  expr Formula
  exists_unique(x : Variable, phi : Formula)
  {
    latex "\\exists! " + $x + " " + $phi;
    bind $x;
  }

  axiom
  existential_uniqueness(x : Variable, phi : Formula,
    y : Variable, phi_0 : Formula)
  {
    require free_for(t($y), t($x), $phi);
    require substitution(t($x), $phi, t($y), $phi_0);

    infer iff(exists_unique($x, $phi), and(exists($x, $phi),
      not(exists($y, and($phi_0, not(eq(t($x), t($y))))))));
  }

  type Predicate1 atomic;
  type Predicate2 atomic;
  type Predicate3 atomic;

  expr Formula
  eval_p1(p : Predicate1, t_1 : Term)
  {
    // require unused($p);
    latex "\\left( " + $p + " \\right)\\left( " + $t_1 + " \\right) ";
  }

  expr Formula
  eval_p2(p : Predicate2, t_1 : Term, t_2 : Term)
  {
    latex "\\left( " + $p + " \\right)\\left( " + $t_1 + " , " + $t_2 +
      " \\right) ";
  }

  expr Formula
  eval_p3(p : Predicate3, t_1 : Term, t_2 : Term, t_3 : Term)
  {
    latex "\\left( " + $p + " \\right)\\left( " + $t_1 + " , " + $t_2 +
      " , " + $t_3 + " \\right) ";
  }

  type Function0 atomic;
  type Function1 atomic;
  type Function2 atomic;
  type Function3 atomic;

  expr Term
  eval_f0(f : Function0)
  {
    latex $f;
  }

  expr Term
  eval_f1(f : Function1, t_1 : Term)
  {
    latex "\\left( " + $f + " \\right)\\left( " + $t_1 + " \\right) ";
  }

  expr Term
  eval_f2(f : Function2, t_1 : Term, t_2 : Term)
  {
    latex "\\left( " + $f + " \\right)\\left( " + $t_1 + " , " + $t_2 +
      " \\right) ";
  }

  expr Term
  eval_f3(f : Function3, t_1 : Term, t_2 : Term, t_3 : Term)
  {
    latex "\\left( " + $f + " \\right)\\left( " + $t_1 + " , " + $t_2 +
      " , " + $t_3 + " \\right) ";
  }

  axiom
  extend_predicate1(p : Predicate1, phi : Formula, x_1 : Variable)
  {
    require cover_free($x_1, $phi);

    infer any($x_1, iff(eval_p1($p, t($x_1)), $phi));
  }

  axiom
  extend_predicate2(p : Predicate2, phi : Formula, x_1 : Variable,
    x_2 : Variable)
  {
    require distinct($x_1, $x_2);
    require cover_free($x_1, $x_2, $phi);

    infer any($x_1, any($x_2, iff(eval_p2($p, t($x_1), t($x_2)), $phi)));
  }

  axiom
  extend_predicate3(p : Predicate3, phi : Formula, x_1 : Variable,
    x_2 : Variable, x_3 : Variable)
  {
    require distinct($x_1, $x_2, $x_3);
    require cover_free($x_1, $x_2, $x_3, $phi);

    infer any($x_1, any($x_2, any($x_3,
      iff(eval_p3($p, t($x_1), t($x_2), t($x_3)), $phi))));
  }

  axiom
  extend_function0(f : Function0, phi : Formula, phi_0 : Formula)
  {
    require free_for(eval_f0($f), t(vars.y), $phi);
    require full_substitution(t(vars.y), $phi, eval_f0($f), $phi_0);

    assume exists_unique(vars.y, $phi);

    infer $phi_0;
  }

  axiom
  extend_function1(f : Function1, phi : Formula, phi_0 : Formula,
    x_1 : Variable)
  {
    require distinct(vars.y, $x_1);
    /* require free($x_1, $phi); */
    /* require cover_free(vars.y, $x_1, $phi); */
    require free_for(eval_f1($f, t($x_1)), t(vars.y), $phi);
    require full_substitution(t(vars.y), $phi, eval_f1($f, t($x_1)), $phi_0);

    assume any($x_1, exists_unique(vars.y, $phi));

    infer any($x_1, $phi_0);
  }

  axiom
  extend_function2(f : Function2, phi : Formula, phi_0 : Formula,
    x_1 : Variable, x_2 : Variable)
  {
    require distinct(vars.y, $x_1, $x_2);
    /* require free($x_1, $phi); */
    /* require free($x_2, $phi); */
    /* require cover_free(vars.y, $x_1, $x_2, $phi); */
    require free_for(eval_f2($f, t($x_1), t($x_2)), t(vars.y), $phi);
    require full_substitution(t(vars.y), $phi,
      eval_f2($f, t($x_1), t($x_2)), $phi_0);

    assume any($x_1, any($x_2, exists_unique(vars.y, $phi)));

    infer any($x_1, any($x_2, $phi_0));
  }

  axiom
  extend_function3(f : Function3, phi : Formula, phi_0 : Formula,
    x_1 : Variable, x_2 : Variable, x_3 : Variable)
  {
    require distinct(vars.y, $x_1, $x_2, $x_3);
    /* require free($x_1, $phi); */
    /* require free($x_2, $phi); */
    /* require free($x_3, $phi); */
    /* require cover_free(vars.y, $x_1, $x_2, $x_3, $phi); */
    require free_for(eval_f3($f, t($x_1), t($x_2), t($x_3)), t(vars.y), $phi);
    require full_substitution(t(vars.y), $phi,
      eval_f3($f, t($x_1), t($x_2), t($x_3)), $phi_0);

    assume any($x_1, any($x_2, any($x_3, exists_unique(vars.y, $phi))));

    infer any($x_1, any($x_2, any($x_3, $phi_0)));
  }
}
/* alias predicate_calculus pred; */

namespace zfc
{
  use propositional_calculus;
  use predicate_calculus;

  const in : Predicate2
  {
    latex "\\in";
  }

  axiom
  extensionality()
  {
    infer any(vars.x, any(vars.y, implies(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y)))), eq(t(vars.x), t(vars.y)))));
  }

  /* TODO: this follows from extensionality. */
  axiom
  set_builder_uniqueness(phi : Formula)
  {
    require not_free(vars.y, $phi);

    infer implies(exists(vars.x, any(vars.y,
      iff(eval_p2(in, t(vars.y), t(vars.x)), $phi))),
      exists_unique(vars.x, any(vars.y,
      iff(eval_p2(in, t(vars.y), t(vars.x)), $phi))));
  }

  theorem
  test(phi : Formula)
  {
    /*infer any(vars.x, any(vars.y, implies(and(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)), $phi)),
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.y)), $phi))),
      eq(t(vars.x), t(vars.y)))));*/

    step extensionality();
    step instantiation_elimination_meta(vars.x,
      any(vars.y, implies(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y)))), eq(t(vars.x), t(vars.y)))));
    step instantiation_elimination_meta(vars.y,
      implies(any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y)))), eq(t(vars.x), t(vars.y))));
  }

  axiom
  regularity()
  {
    def nonempty exists(vars.a, eval_p2(in, t(vars.a), t(vars.x)));

    infer any(vars.x, implies(%nonempty,
      exists(vars.y, and(eval_p2(in, t(vars.y), t(vars.x)),
      not(exists(vars.z, and(eval_p2(in, t(vars.z), t(vars.y)),
      eval_p2(in, t(vars.z), t(vars.y)))))))));
  }

  axiom
  specification(phi : Formula)
  {
    /* require free(vars.x, $phi); */

    infer any(vars.z, exists(vars.y, any(vars.x,
      iff(eval_p2(in, t(vars.x), t(vars.y)),
      and(eval_p2(in, t(vars.x), t(vars.z)), $phi)))));
  }

  const empty : Function0
  {
    latex "\\emptyset";
  }

  namespace lemma
  {
    theorem
    empty_set_exists()
    {
      infer exists(vars.y, any(vars.x, not(eval_p2(in, t(vars.x), t(vars.y)))));

      step specification(F);
      step false();
      step negative_conjunction_introduction(F,
        eval_p2(in, t(vars.x), t(vars.z)));
      step modus_ponens(not(F), not(and(eval_p2(in, t(vars.x), t(vars.z)), F)));
      step instantiation_elimination(vars.z, exists(vars.y, any(vars.x,
        iff(eval_p2(in, t(vars.x), t(vars.y)), and(
        eval_p2(in, t(vars.x), t(vars.z)), F)))));
      step modus_ponens(any(vars.z, exists(vars.y, any(vars.x,
        iff(eval_p2(in, t(vars.x), t(vars.y)), and(
        eval_p2(in, t(vars.x), t(vars.z)), F))))),
        exists(vars.y, any(vars.x,
        iff(eval_p2(in, t(vars.x), t(vars.y)), and(
        eval_p2(in, t(vars.x), t(vars.z)), F)))));
      step identity(iff(eval_p2(in, t(vars.x), t(vars.y)), and(
        eval_p2(in, t(vars.x), t(vars.z)), F)));
      step infer_negated_equivalent(iff(eval_p2(in, t(vars.x), t(vars.y)), and(
        eval_p2(in, t(vars.x), t(vars.z)), F)),
        eval_p2(in, t(vars.x), t(vars.y)), and(
        eval_p2(in, t(vars.x), t(vars.z)), F));
      step implication_generalization(vars.x, iff(eval_p2(in, t(vars.x),
        t(vars.y)), and(eval_p2(in, t(vars.x), t(vars.z)), F)),
        not(eval_p2(in, t(vars.x), t(vars.y))));
      step implication_generalization_existential(vars.y,
        any(vars.x, iff(eval_p2(in, t(vars.x),
        t(vars.y)), and(eval_p2(in, t(vars.x), t(vars.z)), F))),
        any(vars.x, not(eval_p2(in, t(vars.x), t(vars.y)))));
      step modus_ponens(exists(vars.y, any(vars.x,
        iff(eval_p2(in, t(vars.x), t(vars.y)), and(
        eval_p2(in, t(vars.x), t(vars.z)), F)))),
        exists(vars.y, any(vars.x, not(eval_p2(in, t(vars.x), t(vars.y))))));
    }

    /* TODO: this can be inferred from set_builder_uniqueness. */
    axiom
    empty_set_unique()
    {
      infer exists_unique(vars.y, any(vars.x,
        not(eval_p2(in, t(vars.x), t(vars.y)))));
    }
  }

  theorem
  empty_set()
  {
    infer any(vars.x, not(eval_p2(in, t(vars.x), eval_f0(empty))));

    step lemma.empty_set_exists();
    step lemma.empty_set_unique();
    step extend_function0(empty,
      any(vars.x, not(eval_p2(in, t(vars.x), t(vars.y)))),
      any(vars.x, not(eval_p2(in, t(vars.x), eval_f0(empty)))));
  }

  axiom
  pairing()
  {
    infer any(vars.x, any(vars.y, exists(vars.z, and(
      eval_p2(in, t(vars.x), t(vars.z)),
      eval_p2(in, t(vars.y), t(vars.z))))));
  }

  const singleton : Function1
  {
    latex "\\{ \\cdot_1 \\}";
  }

  namespace lemma
  {
    /* TODO: prove this from pairing. */
    axiom
    singleton_exists()
    {
      infer any(vars.a, exists(vars.y, any(vars.x, iff(
        eval_p2(in, t(vars.x), t(vars.y)), eq(t(vars.x), t(vars.a))))));
    }

    axiom
    singleton_unique()
    {
      infer any(vars.a, exists_unique(vars.y, any(vars.x, iff(
        eval_p2(in, t(vars.x), t(vars.y)), eq(t(vars.x), t(vars.a))))));
    }
  }

  theorem
  singleton_containing()
  {
    infer any(vars.a, any(vars.x, iff(eval_p2(in, t(vars.x),
      eval_f1(singleton, t(vars.a))), eq(t(vars.x), t(vars.a)))));

    step lemma.singleton_unique();
    step extend_function1(singleton, any(vars.x, iff(
      eval_p2(in, t(vars.x), t(vars.y)), eq(t(vars.x), t(vars.a)))),
      any(vars.x, iff(eval_p2(in, t(vars.x), eval_f1(singleton, t(vars.a))),
      eq(t(vars.x), t(vars.a)))), vars.a);
  }

  const pair : Function2
  {
    latex "\\{ \\cdot_1 , \\cdot_2 \\}";
  }

  namespace lemma
  {
    /* TODO: prove this from pairing. */
    axiom pair_exists()
    {
      infer any(vars.a, any(vars.b, exists(vars.y, any(vars.x,
        iff(eval_p2(in, t(vars.x), t(vars.y)),
        or(eq(t(vars.x), t(vars.a)), eq(t(vars.x), t(vars.b))))))));
    }

    axiom pair_unique()
    {
    infer any(vars.a, any(vars.b, exists_unique(vars.y, any(vars.x,
      iff(eval_p2(in, t(vars.x), t(vars.y)),
      or(eq(t(vars.x), t(vars.a)), eq(t(vars.x), t(vars.b))))))));
    }
  }

  theorem
  pair_containing()
  {
    infer any(vars.a, any(vars.b, any(vars.x, iff(
      eval_p2(in, t(vars.x), eval_f2(pair, t(vars.a), t(vars.b))),
      or(eq(t(vars.x), t(vars.a)), eq(t(vars.x), t(vars.b)))))));

    step lemma.pair_unique();
    step extend_function2(pair, any(vars.x, iff(
      eval_p2(in, t(vars.x), t(vars.y)),
      or(eq(t(vars.x), t(vars.a)), eq(t(vars.x), t(vars.b))))),
      any(vars.x, iff(eval_p2(in, t(vars.x),
      eval_f2(pair, t(vars.a), t(vars.b))), or(eq(t(vars.x), t(vars.a)),
      eq(t(vars.x), t(vars.b))))), vars.a, vars.b);
  }

  axiom
  replacement(phi : Formula)
  {
    //require free(vars.x, $phi);
    //require free(vars.y, $phi);
    //require free(vars.A, $phi);
    //require not_free(vars.B, $phi);

    infer any(vars.A, implies(any(vars.x, implies(
      eval_p2(in, t(vars.x), t(vars.A)), exists_unique(vars.y, $phi))),
      exists(vars.B, any(vars.x, implies(eval_p2(in, t(vars.x), t(vars.A)),
      exists(vars.y, and(eval_p2(in, t(vars.y), t(vars.B)), $phi)))))));
  }

  const successor : Function1
  {
    latex "S";
  }

  /*
  axiom
  infinity()
  {
    infer exists(vars.X, and(eval_p2(in, empty, t(vars.X)),
      any(vars.y,
      implies(eval_p2(in, t(vars.y), t(vars.X)),
      eval_p2(in, eval_f1(successor, t(vars.y)), t(vars.X))))));
  }
  */

  const subset : Predicate2
  {
    latex "\\subset";
  }

  theorem
  subset_of()
  {
    infer any(vars.x, any(vars.y,
      iff(eval_p2(subset, t(vars.x), t(vars.y)),
      any(vars.z, implies(eval_p2(in, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y)))))));

    step extend_predicate2(subset, any(vars.z, implies(eval_p2(in, t(vars.z),
      t(vars.x)), eval_p2(in, t(vars.z), t(vars.y)))), vars.x, vars.y);
  }

  axiom
  power_set()
  {
    infer any(vars.x, exists(vars.y, any(vars.z,
      implies(eval_p2(subset, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y))))));
  }

  const union : Function1
  {
    latex "\\cup \\cdot_1";
  }

  /* TODO: prove from the axiom of union. */
  axiom
  union_of_elements()
  {
    infer any(vars.a, any(vars.x, iff(eval_p2(in, t(vars.x),
      eval_f1(union, t(vars.a))), exists(vars.z, and(
      eval_p2(in, t(vars.x), t(vars.z)),
      eval_p2(in, t(vars.z), t(vars.a)))))));
  }

  const naturals_ordinals : Function0
  {
    latex "\\mathbb{N}";
  }

  const zero_ordinal : Function0
  {
    latex "0";
  }

  const ordered_pair : Function2
  {
    latex "\\cdot_1 , \\cdot_2";
  }

  const cartesian_product : Function2
  {
    latex "\\cdot_1 \\times \\cdot_2";
  }

  axiom
  cartesian_product_of_sets()
  {
    infer any(vars.A, any(vars.B, any(vars.x, iff(
      eval_p2(in, t(vars.x), eval_f2(cartesian_product, t(vars.A), t(vars.B))),
      exists(vars.a, exists(vars.b, and(and(eval_p2(in, t(vars.a), t(vars.A)),
      eval_p2(in, t(vars.b), t(vars.B))), eq(t(vars.x),
      eval_f2(ordered_pair, t(vars.a), t(vars.b))))))))));
  }

  const map : Predicate3
  {
    latex "\\cdot_1 : \\cdot_2 \\to \\cdot_3";
  }

  axiom
  map_of_sets()
  {
    infer any(vars.f, any(vars.X, any(vars.Y, iff(
      eval_p3(map, t(vars.f), t(vars.X), t(vars.Y)),
      any(vars.x, implies(eval_p2(in, t(vars.x), t(vars.X)),
      exists_unique(vars.y, and(eval_p2(in, t(vars.y), t(vars.Y)),
      eval_p2(in, eval_f2(ordered_pair, t(vars.x), t(vars.y)),
      t(vars.f))))))))));
  }

  const eval_map : Function2
  {
    latex "\\cdot_1 \\left( \\cdot_2 \\right)";
  }
}

namespace algebra
{
  use propositional_calculus;
  use predicate_calculus;
  use zfc;

  const binary : Predicate2
  {
    latex "\\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2";
  }

  theorem
  binary_operation()
  {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary, t(vars.f), t(vars.X)),
      eval_p3(map, t(vars.f), eval_f2(cartesian_product, t(vars.X), t(vars.X)),
      t(vars.X)))));

    step extend_predicate2(binary, eval_p3(map, t(vars.f),
      eval_f2(cartesian_product, t(vars.X), t(vars.X)), t(vars.X)),
      vars.f, vars.X);
  }

  const binary_commutative : Predicate2
  {
    latex "\\mathrm{comm} \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem
  binary_operation_commutative()
  {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary_commutative, t(vars.f),
      t(vars.X)), and(eval_p2(binary, t(vars.f), t(vars.X)),
      any(vars.x, any(vars.y, implies(eval_p2(in,
      eval_f2(ordered_pair, t(vars.x), t(vars.y)),
      eval_f2(cartesian_product, t(vars.X), t(vars.X))), eq(
      eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.x), t(vars.y))),
      eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.y),
      t(vars.x)))))))))));

    step extend_predicate2(binary_commutative,
      and(eval_p2(binary, t(vars.f), t(vars.X)),
      any(vars.x, any(vars.y, implies(eval_p2(in,
      eval_f2(ordered_pair, t(vars.x), t(vars.y)),
      eval_f2(cartesian_product, t(vars.X), t(vars.X))), eq(
      eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.x), t(vars.y))),
      eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.y),
      t(vars.x)))))))), vars.f, vars.X);
  }

  const binary_associative : Predicate2
  {
    latex "\\mathrm{assoc} \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem
  binary_operation_associative()
  {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary_associative, t(vars.f),
      t(vars.X)), any(vars.x, any(vars.y, any(vars.z, implies(and(
      eval_p2(in, t(vars.x), t(vars.X)), and(
      eval_p2(in, t(vars.y), t(vars.X)), eval_p2(in, t(vars.z), t(vars.X)))),
      eq(eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, eval_f2(eval_map,
      t(vars.f), eval_f2(ordered_pair, t(vars.x), t(vars.y))),
      t(vars.z))),
      eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.x),
      eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.y),
      t(vars.z)))))))))))));

    step extend_predicate2(binary_associative,
      any(vars.x, any(vars.y, any(vars.z, implies(and(
      eval_p2(in, t(vars.x), t(vars.X)), and(
      eval_p2(in, t(vars.y), t(vars.X)), eval_p2(in, t(vars.z), t(vars.X)))),
      eq(eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, eval_f2(eval_map,
      t(vars.f), eval_f2(ordered_pair, t(vars.x), t(vars.y))),
      t(vars.z))),
      eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.x),
      eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.y),
      t(vars.z)))))))))), vars.f, vars.X);
  }

  const binary_has_left_identity : Predicate2
  {
    latex "1_{\\mathrm{L}} \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem
  binary_operation_has_left_identity()
  {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary_has_left_identity,
      t(vars.f), t(vars.X)), and(eval_p2(binary, t(vars.f), t(vars.X)),
      exists(vars.e, any(vars.x, implies(eval_p2(in, t(vars.x), t(vars.X)),
      eq(eval_f2(eval_map, t(vars.f),
      eval_f2(ordered_pair, t(vars.e), t(vars.x))), t(vars.x)))))))));

    step extend_predicate2(binary_has_left_identity,
      and(eval_p2(binary, t(vars.f), t(vars.X)),
      exists(vars.e, any(vars.x, implies(eval_p2(in, t(vars.x), t(vars.X)),
      eq(eval_f2(eval_map, t(vars.f),
      eval_f2(ordered_pair, t(vars.e), t(vars.x))), t(vars.x)))))),
      vars.f, vars.X);
  }

  const binary_has_right_identity : Predicate2
  {
    latex "1_{\\mathrm{R}} \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem
  binary_operation_has_right_identity()
  {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary_has_right_identity,
      t(vars.f), t(vars.X)), and(eval_p2(binary, t(vars.f), t(vars.X)),
      exists(vars.e, any(vars.x, implies(eval_p2(in, t(vars.x), t(vars.X)),
      eq(eval_f2(eval_map, t(vars.f),
      eval_f2(ordered_pair, t(vars.x), t(vars.e))), t(vars.x)))))))));

    step extend_predicate2(binary_has_right_identity,
      and(eval_p2(binary, t(vars.f), t(vars.X)),
      exists(vars.e, any(vars.x, implies(eval_p2(in, t(vars.x), t(vars.X)),
      eq(eval_f2(eval_map, t(vars.f),
      eval_f2(ordered_pair, t(vars.x), t(vars.e))), t(vars.x)))))),
      vars.f, vars.X);
  }

  const binary_has_identity : Predicate2
  {
    latex "1 \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem
  binary_operation_has_identity()
  {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary_has_identity,
      t(vars.f), t(vars.X)), and(eval_p2(binary_has_left_identity,
      t(vars.f), t(vars.X)), eval_p2(binary_has_right_identity,
      t(vars.f), t(vars.X))))));

    step extend_predicate2(binary_has_identity,
      and(eval_p2(binary_has_left_identity,
      t(vars.f), t(vars.X)), eval_p2(binary_has_right_identity,
      t(vars.f), t(vars.X))), vars.f, vars.X);
  }

  const is_group : Predicate2
  {
    latex "\\mathrm{grp} \\left( \\cdot_1 , \\cdot_2 \\right)";
  }
}
