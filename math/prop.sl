/*

Propositional Calculus:

Postulate rules for forming formulas, using negation and implication. Then
add the axioms for propositional calculus. These are axioms P2, P3, and P4
as shown in:
  https://en.wikipedia.org/wiki/Hilbert_system.

Axiom P1 is proven as `identity`. We then extend our system to include the
connectives "if and only if", "or", and "and".

*/
namespace propositional_calculus {
  type Formula;

  expr Formula implies(phi : Formula, psi : Formula) {
    latex "\\left( " + $phi + " \\implies " + $psi + " \\right)";
  }

  expr Formula not(phi : Formula) {
    latex "\\neg " + $phi;
  }

  axiom modus_ponens(phi : Formula, psi : Formula) {
    assume $phi;
    assume implies($phi, $psi);

    infer $psi;
  }

  axiom simplification(phi : Formula, psi : Formula) {
    infer implies($phi, implies($psi, $phi));
  }

  axiom distributive(phi : Formula, psi : Formula, chi : Formula) {
    def A implies($phi, implies($psi, $chi));
    def B implies(implies($phi, $psi), implies($phi, $chi));

    infer implies(%A, %B);
  }

  axiom transposition(phi : Formula, psi : Formula) {
    infer implies(implies(not($psi), not($phi)), implies($phi, $psi));
  }

  const T : Formula {
    latex "\\top";
  }

  axiom true() {
    infer T;
  }

  const F : Formula {
    latex "\\bot";
  }

  axiom false() {
    infer not(F);
  }

  /*

  Some of my own common theorems.

  */
  theorem false_implies(phi : Formula) {
    infer implies(F, $phi);

    step transposition(F, $phi);
    step simplification(not(F), not($phi));
    step false();
    step modus_ponens(not(F), implies(not($phi), not(F)));
    step modus_ponens(implies(not($phi), not(F)), implies(F, $phi));
  }

  theorem implies_true_formula(phi : Formula, psi : Formula) {
    assume $psi;

    infer implies($phi, $psi);

    step simplification($psi, $phi);
    step modus_ponens($psi, implies($phi, $psi));
  }

  theorem implies_true(phi : Formula) {
    infer implies($phi, T);

    step true();
    step implies_true_formula($phi, T);
  }

  /*

  Common theorems of propositional calculus, based on the list given in
  https://en.wikipedia.org/wiki/Hilbert_system

  */
  theorem identity(phi : Formula) {
    infer implies($phi, $phi);

    step simplification($phi, implies($phi, $phi));
    step distributive($phi, implies($phi, $phi), $phi);
    step modus_ponens(implies($phi, implies(implies($phi, $phi), $phi)),
        implies(implies($phi, implies($phi, $phi)), implies($phi, $phi)));
    step simplification($phi, $phi);
    step modus_ponens(implies($phi, implies($phi, $phi)), implies($phi, $phi));
  }

  theorem hypothetical_syllogism(phi : Formula, psi : Formula,
      chi : Formula) {
    infer implies(implies($psi, $chi),
        implies(implies($phi, $psi), implies($phi, $chi)));

    step distributive($phi, $psi, $chi);
    step simplification(implies(implies($phi, implies($psi, $chi)),
        implies(implies($phi, $psi), implies($phi, $chi))),
        implies($psi, $chi));
    step modus_ponens(implies(implies($phi, implies($psi, $chi)),
        implies(implies($phi, $psi), implies($phi, $chi))),
        implies(implies($psi, $chi), implies(implies($phi,
        implies($psi, $chi)), implies(implies($phi, $psi),
        implies($phi, $chi)))));
    step distributive(implies($psi, $chi), implies($phi, implies($psi, $chi)),
        implies(implies($phi, $psi), implies($phi, $chi)));
    step modus_ponens(implies(implies($psi, $chi), implies(implies($phi,
        implies($psi, $chi)), implies(implies($phi, $psi),
        implies($phi, $chi)))), implies(implies(implies($psi, $chi),
        implies($phi, implies($psi, $chi))), implies(implies($psi, $chi),
        implies(implies($phi, $psi), implies($phi, $chi)))));
    step simplification(implies($psi, $chi), $phi);
    step modus_ponens(implies(implies($psi, $chi),
        implies($phi, implies($psi, $chi))),
        implies(implies($psi, $chi), implies(implies($phi, $psi),
        implies($phi, $chi))));
  }

  theorem hypothetical_syllogism_meta(phi : Formula, psi : Formula,
      chi : Formula) {
    assume implies($psi, $chi);
    assume implies($phi, $psi);

    infer implies($phi, $chi);

    step hypothetical_syllogism($phi, $psi, $chi);
    step modus_ponens(implies($psi, $chi),
        implies(implies($phi, $psi), implies($phi, $chi)));
    step modus_ponens(implies($phi, $psi), implies($phi, $chi));
  }

  theorem double_simplification(phi : Formula, psi : Formula) {
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

  theorem double_negation_left(phi : Formula) {
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

  theorem double_negation_right(phi : Formula) {
    infer implies($phi, not(not($phi)));

    step double_negation_left(not($phi));
    step transposition($phi, not(not($phi)));
    step modus_ponens(implies(not(not(not($phi))), not($phi)),
        implies($phi, not(not($phi))));
  }

  theorem implication_commutation(phi : Formula, psi : Formula,
      chi : Formula) {
    infer implies(implies($phi, implies($psi, $chi)),
        implies($psi, implies($phi, $chi)));

    step distributive($phi, $psi, $chi);
    step hypothetical_syllogism($psi, implies($phi, $psi),
        implies($phi, $chi));
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

  theorem hypothetical_syllogism_2(phi : Formula, psi : Formula,
      chi : Formula) {
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

  theorem transposition_2(phi : Formula, psi : Formula) {
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

  theorem modus_tollens(phi : Formula, psi : Formula) {
    assume implies($phi, $psi);
    assume not($psi);

    infer not($phi);

    step transposition_2($phi, $psi);
    step modus_ponens(implies($phi, $psi), implies(not($psi), not($phi)));
    step modus_ponens(not($psi), not($phi));
  }

  theorem transposition_3(phi : Formula, psi : Formula) {
    infer implies(implies(not($phi), $psi), implies(not($psi), $phi));

    step transposition_2(not($phi), $psi);
    step double_negation_left($phi);
    step hypothetical_syllogism(not($psi), not(not($phi)), $phi);
    step modus_ponens(implies(not(not($phi)), $phi),
        implies(implies(not($psi), not(not($phi))), implies(not($psi), $phi)));
    step hypothetical_syllogism_meta(implies(not($phi), $psi),
        implies(not($psi), not(not($phi))), implies(not($psi), $phi));
  }

  theorem contradiction(phi : Formula) {
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

  theorem intermediate_elimination(phi : Formula, psi : Formula,
      chi : Formula) {
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
  theorem triple_antecedent_introduction_meta(phi : Formula, psi : Formula,
      chi : Formula, theta : Formula) {
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
  expr Formula and(phi : Formula, psi : Formula) {
    as not(implies($phi, not($psi)));
    latex "\\left( " + $phi + " \\land " + $psi + " \\right)";
  }

  axiom conjunction_introduction(phi : Formula, psi : Formula) {
    infer implies($phi, implies($psi, and($phi, $psi)));
  }

  theorem hypothetical_conjunction_introduction(phi : Formula,
      psi : Formula, chi : Formula) {
    infer implies(implies($phi, $psi), implies(implies($phi, $chi),
        implies($phi, and($psi, $chi))));

    step conjunction_introduction($psi, $chi);
    step triple_antecedent_introduction_meta($psi, $chi, and($psi, $chi),
        $phi);
  }

  theorem conjunction_introduction_meta(phi : Formula, psi : Formula) {
    assume $phi;
    assume $psi;

    infer and($phi, $psi);

    step conjunction_introduction($phi, $psi);
    step modus_ponens($phi, implies($psi, and($phi, $psi)));
    step modus_ponens($psi, and($phi, $psi));
  }

  theorem conjunction_elimination_right(phi : Formula, psi : Formula) {
    infer implies(and($phi, $psi), $psi);

    step simplification(not($psi), $phi);
    step transposition_2(not($psi), implies($phi, not($psi)));
    step modus_ponens(implies(not($psi), implies($phi, not($psi))),
        implies(not(implies($phi, not($psi))), not(not($psi))));
    step double_negation_left($psi);
    step hypothetical_syllogism_meta(not(implies($phi, not($psi))),
        not(not($psi)), $psi);
  }

  theorem conjunction_elimination_right_meta(phi : Formula, psi : Formula) {
    assume and($phi, $psi);

    infer $psi;

    step conjunction_elimination_right($phi, $psi);
    step modus_ponens(and($phi, $psi), $psi);
  }

  theorem conjunction_elimination_left(phi : Formula, psi : Formula) {
    infer implies(and($phi, $psi), $phi);

    step double_negation_left($psi);
    step hypothetical_syllogism_2(not(not($psi)), $psi, not($phi));
    step modus_ponens(implies(not(not($psi)), $psi),
        implies(implies($psi, not($phi)), implies(not(not($psi)), not($phi))));
    step transposition_2(implies($psi, not($phi)),
        implies(not(not($psi)), not($phi)));
    step modus_ponens(implies(implies($psi, not($phi)),
        implies(not(not($psi)), not($phi))),
        implies(not(implies(not(not($psi)), not($phi))),
        not(implies($psi, not($phi)))));
    step transposition($phi, not($psi));
    step transposition_2(implies(not(not($psi)), not($phi)),
        implies($phi, not($psi)));
    step modus_ponens(implies(implies(not(not($psi)), not($phi)),
        implies($phi, not($psi))),
        implies(not(implies($phi, not($psi))),
        not(implies(not(not($psi)), not($phi)))));
    step hypothetical_syllogism_meta(not(implies($phi, not($psi))),
        not(implies(not(not($psi)), not($phi))),
        not(implies($psi, not($phi))));
    step conjunction_elimination_right($psi, $phi);
    step hypothetical_syllogism_meta(and($phi, $psi),
        and($psi, $phi), $phi);
  }

  theorem conjunction_elimination_left_meta(phi : Formula, psi : Formula) {
    assume and($phi, $psi);

    infer $phi;

    step conjunction_elimination_left($phi, $psi);
    step modus_ponens(and($phi, $psi), $phi);
  }

  theorem conjunction_elimination_meta(phi : Formula, psi : Formula) {
    assume and($phi, $psi);

    infer $phi;
    infer $psi;

    step conjunction_elimination_left_meta($phi, $psi);
    step conjunction_elimination_right_meta($phi, $psi);
  }

  theorem negative_conjunction_introduction(phi : Formula, psi : Formula) {
    infer implies(not($phi), not(and($psi, $phi)));

    step conjunction_elimination_right($psi, $phi);
    step transposition_2(and($psi, $phi), $phi);
    step modus_ponens(implies(and($psi, $phi), $phi),
        implies(not($phi), not(and($psi, $phi))));
  }

  theorem conjunction_implication_distributive(phi : Formula, psi : Formula,
      chi : Formula) {
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

  theorem conjunction_implication_distributive_meta(phi : Formula,
      psi : Formula, chi : Formula) {
    assume implies($phi, $psi);
    assume implies($phi, $chi);

    infer implies($phi, and($psi, $chi));

    step conjunction_implication_distributive($phi, $psi, $chi);
    step conjunction_introduction_meta(implies($phi, $psi),
        implies($phi, $chi));
    step modus_ponens(and(implies($phi, $psi), implies($phi, $chi)),
        implies($phi, and($psi, $chi)));
  }

  expr Formula or(phi : Formula, psi : Formula) {
    as implies(not($phi), $psi);
    latex "\\left( " + $phi + " \\lor " + $psi + " \\right)";
  }

  theorem disjunction_introduction_left(phi : Formula, psi : Formula) {
    infer implies($phi, or($phi, $psi));

    step simplification($phi, not($psi));
    step transposition_3($psi, $phi);
    step hypothetical_syllogism_meta($phi, or($psi, $phi), or($phi, $psi));
  }

  theorem disjunction_introduction_left_meta(phi : Formula, psi : Formula) {
    assume $phi;

    infer or($phi, $psi);

    step disjunction_introduction_left($phi, $psi);
    step modus_ponens($phi, or($phi, $psi));
  }

  theorem disjunction_introduction_right(phi : Formula, psi : Formula) {
    infer implies($psi, or($phi, $psi));

    step simplification($psi, not($phi));
  }

  theorem disjunction_introduction_right_meta(phi : Formula, psi : Formula) {
    assume $psi;

    infer or($phi, $psi);

    step disjunction_introduction_right($phi, $psi);
    step modus_ponens($psi, or($phi, $psi));
  }

  axiom disjunction_elimination(phi : Formula, psi : Formula, chi : Formula) {
    infer implies(implies(implies($phi, $chi), implies($psi, $chi)),
        implies(or($phi, $psi), $chi));
  }

  theorem disjunction_elimination_meta(phi : Formula, psi : Formula,
      chi : Formula) {
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

  expr Formula iff(phi : Formula, psi : Formula) {
    as and(implies($phi, $psi), implies($psi, $phi));
    latex "\\left( " + $phi + " \\iff " + $psi + " \\right)";
  }

  theorem biconditional_introduction(phi : Formula, psi : Formula) {
    infer implies(and(implies($phi, $psi), implies($psi, $phi)),
        iff($phi, $psi));

    step identity(iff($phi, $psi));
  }

  theorem biconditional_introduction_meta(phi : Formula, psi : Formula) {
    assume implies($phi, $psi);
    assume implies($psi, $phi);

    infer iff($phi, $psi);

    step conjunction_introduction_meta(implies($phi, $psi),
        implies($psi, $phi));
    step biconditional_introduction($phi, $psi);
    step modus_ponens(and(implies($phi, $psi), implies($psi, $phi)),
        iff($phi, $psi));
  }

  theorem biconditional_elimination_left(phi : Formula, psi : Formula) {
    infer implies(iff($phi, $psi), implies($psi, $phi));

    step conjunction_elimination_right(implies($phi, $psi),
        implies($psi, $phi));
  }

  theorem biconditional_elimination_left_meta(phi : Formula, psi : Formula) {
    assume iff($phi, $psi);

    infer implies($psi, $phi);

    step biconditional_elimination_left($phi, $psi);
    step modus_ponens(iff($phi, $psi), implies($psi, $phi));
  }

  theorem biconditional_elimination_right(phi : Formula, psi : Formula) {
    infer implies(iff($phi, $psi), implies($phi, $psi));

    step conjunction_elimination_left(implies($phi, $psi),
        implies($psi, $phi));
  }

  theorem biconditional_elimination_right_meta(phi : Formula, psi : Formula) {
    assume iff($phi, $psi);

    infer implies($phi, $psi);

    step biconditional_elimination_right($phi, $psi);
    step modus_ponens(iff($phi, $psi), implies($phi, $psi));
  }

  theorem biconditional_elimination_meta(phi : Formula, psi : Formula) {
    assume iff($phi, $psi);

    infer implies($psi, $phi);
    infer implies($phi, $psi);

    step biconditional_elimination_left_meta($phi, $psi);
    step biconditional_elimination_right_meta($phi, $psi);
  }

  theorem biconditional_distribution_left(phi : Formula, psi : Formula,
      chi : Formula) {
    infer implies(iff($phi, $psi),
        implies(implies($phi, $chi), implies($psi, $chi)));

    step biconditional_elimination_left($phi, $psi);
    step hypothetical_syllogism_2($psi, $phi, $chi);
    step hypothetical_syllogism_meta(iff($phi, $psi), implies($psi, $phi),
        implies(implies($phi, $chi), implies($psi, $chi)));
  }

  theorem biconditional_distribution_right(phi : Formula, psi : Formula,
      chi : Formula) {
    infer implies(iff($phi, $psi),
        implies(implies($chi, $phi), implies($chi, $psi)));

    step biconditional_elimination_right($phi, $psi);
    step hypothetical_syllogism($chi, $phi, $psi);
    step hypothetical_syllogism_meta(iff($phi, $psi), implies($phi, $psi),
        implies(implies($chi, $phi), implies($chi, $psi)));
  }

  theorem infer_negated_equivalent(phi : Formula, psi : Formula,
      chi : Formula) {
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

  namespace lemma {
    theorem conjunction_commutation_l1(phi : Formula, psi : Formula) {
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

  theorem conjunction_commutation(phi : Formula, psi : Formula) {
    infer iff(and($phi, $psi), and($psi, $phi));
    infer implies(and($phi, $psi), and($psi, $phi));
    infer implies(and($psi, $phi), and($phi, $psi));

    step lemma.conjunction_commutation_l1($phi, $psi);
    step lemma.conjunction_commutation_l1($psi, $phi);
    step biconditional_introduction_meta(and($phi, $psi), and($psi, $phi));
  }

  namespace lemma {
    theorem conjunction_biconditional_elimination_l1(phi : Formula,
        psi : Formula, chi : Formula) {
      infer implies(and(iff($psi, $phi), iff($chi, $phi)),
          implies($psi, $chi));

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
          implies($psi, $phi), implies(implies($phi, $chi),
          implies($psi, $chi)));
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

  theorem conjunction_biconditional_elimination(phi : Formula, psi : Formula,
      chi : Formula) {
    infer implies(and(iff($psi, $phi), iff($chi, $phi)), iff($psi, $chi));

    step lemma.conjunction_biconditional_elimination_l1($phi, $psi, $chi);
    step lemma.conjunction_biconditional_elimination_l1($phi, $chi, $psi);
    step lemma.conjunction_commutation_l1(iff($psi, $phi), iff($chi, $phi));
    step hypothetical_syllogism_meta(and(iff($psi, $phi), iff($chi, $phi)),
        and(iff($chi, $phi), iff($psi, $phi)), implies($chi, $psi));
    step conjunction_implication_distributive_meta(and(iff($psi, $phi),
        iff($chi, $phi)), implies($psi, $chi), implies($chi, $psi));
    step biconditional_introduction($psi, $chi);
    step hypothetical_syllogism_meta(and(iff($psi, $phi), iff($chi, $phi)),
        and(implies($psi, $chi), implies($chi, $psi)), iff($psi, $chi));
  }

  namespace lemma {
    theorem biconditional_commutation_l1(phi : Formula, psi : Formula) {
      infer implies(iff($phi, $psi), iff($psi, $phi));

      step biconditional_elimination_left($phi, $psi);
      step biconditional_elimination_right($phi, $psi);
      step conjunction_implication_distributive_meta(iff($phi, $psi),
          implies($phi, $psi), implies($psi, $phi));
      step conjunction_commutation_l1(implies($phi, $psi),
          implies($psi, $phi));
      step hypothetical_syllogism_meta(iff($phi, $psi),
          and(implies($phi, $psi), implies($psi, $phi)),
          and(implies($psi, $phi), implies($phi, $psi)));
      step biconditional_introduction($psi, $phi);
      step hypothetical_syllogism_meta(iff($phi, $psi),
          and(implies($psi, $phi), implies($phi, $psi)),
          iff($psi, $phi));
    }
  }

  theorem biconditional_commutation(phi : Formula, psi : Formula) {
    infer iff(iff($phi, $psi), iff($psi, $phi));

    step lemma.biconditional_commutation_l1($phi, $psi);
    step lemma.biconditional_commutation_l1($psi, $phi);
    step biconditional_introduction_meta(iff($phi, $psi), iff($psi, $phi));
  }

  theorem conjunction_simplification(phi : Formula, psi : Formula,
      chi : Formula) {
    infer implies(implies($phi, $psi), implies(and($chi, $phi), $psi));

    step conjunction_elimination_right($chi, $phi);
    step hypothetical_syllogism_2(and($chi, $phi), $phi, $psi);
    step modus_ponens(implies(and($chi, $phi), $phi),
        implies(implies($phi, $psi), implies(and($chi, $phi), $psi)));
  }

  theorem conjunction_simplification_2(phi : Formula, psi : Formula,
      chi : Formula) {
    infer implies(implies($phi, $psi), implies(and($chi, $phi),
        and($chi, $psi)));

    step conjunction_introduction($chi, $psi);
    step conjunction_elimination_left($chi, $phi);
    step hypothetical_syllogism_meta(and($chi, $phi), $chi,
        implies($psi, and($chi, $psi)));
    step distributive(and($chi, $phi), $psi, and($chi, $psi));
    step modus_ponens(implies(and($chi, $phi), implies($psi, and($chi, $psi))),
        implies(implies(and($chi, $phi), $psi),
        implies(and($chi, $phi), and($chi, $psi))));
    step conjunction_simplification($phi, $psi, $chi);
    step hypothetical_syllogism_meta(implies($phi, $psi),
        implies(and($chi, $phi), $psi),
        implies(and($chi, $phi), and($chi, $psi)));
  }

  namespace lemma {
    theorem conjunction_biconditional_simplification_l1(phi : Formula,
        psi : Formula, chi : Formula) {
      infer implies(iff($phi, $psi), implies(and($chi, $phi),
          and($chi, $psi)));

      step biconditional_elimination_right($phi, $psi);
      step conjunction_simplification_2($phi, $psi, $chi);
      step hypothetical_syllogism_meta(iff($phi, $psi), implies($phi, $psi),
          implies(and($chi, $phi), and($chi, $psi)));
    }
  }

  theorem conjunction_biconditional_simplification(phi : Formula,
      psi : Formula, chi : Formula) {
    infer implies(iff($phi, $psi), iff(and($chi, $phi), and($chi, $psi)));

    step lemma.conjunction_biconditional_simplification_l1($phi, $psi, $chi);
    step lemma.conjunction_biconditional_simplification_l1($psi, $phi, $chi);
    step lemma.biconditional_commutation_l1($phi, $psi);
    step hypothetical_syllogism_meta(iff($phi, $psi), iff($psi, $phi),
        implies(and($chi, $psi), and($chi, $phi)));
    step conjunction_implication_distributive_meta(iff($phi, $psi),
        implies(and($chi, $phi), and($chi, $psi)),
        implies(and($chi, $psi), and($chi, $phi)));
    step biconditional_introduction(and($chi, $phi), and($chi, $psi));
    step hypothetical_syllogism_meta(iff($phi, $psi),
        and(implies(and($chi, $phi), and($chi, $psi)),
        implies(and($chi, $psi), and($chi, $phi))),
        iff(and($chi, $phi), and($chi, $psi)));
  }

  theorem double_negation(phi : Formula) {
    infer iff($phi, not(not($phi)));

    step double_negation_left($phi);
    step double_negation_right($phi);
    step biconditional_introduction_meta($phi, not(not($phi)));
  }

  theorem false_conjunction(phi : Formula) {
    infer iff(and($phi, F), F);

    step conjunction_elimination_right($phi, F);
    step false_implies(and($phi, F));
    step biconditional_introduction_meta(and($phi, F), F);
  }
}
