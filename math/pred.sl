/*

First Order Logic (with Equality):

Define terms, variables, and quantification. After developing the rules
for free and bound variables, add the axioms for first order logic with
equality. The axioms are taken from Mendelson, pgs. 69-70 and 95.

*/
import "prop.sl";
namespace predicate_calculus {
  use propositional_calculus;

  type Term;
  type Variable atomic binds dummy;

  constspace vars Variable;

  expr Term t(x : Variable) {
    latex $x;
  }

  expr Formula any(x : Variable, phi : Formula) {
    latex "\\forall " + $x + " " + $phi;
    bind $x;
  }

  axiom instantiation(x : Variable, phi : Formula, t : Term, phi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require full_substitution(t($x), $phi, $t, $phi_0);

    infer implies(any($x, $phi), $phi_0);
  }

  axiom quantified_implication(x : Variable, phi : Formula, psi : Formula) {
    infer implies(any($x, implies($phi, $psi)),
        implies(any($x, $phi), any($x, $psi)));
  }

  axiom bound_generalization(x : Variable, phi : Formula) {
    require not_free($x, $phi);

    infer implies($phi, any($x, $phi));
  }

  axiom generalization(x : Variable, phi : Formula) {
    assume $phi;

    infer any($x, $phi);
  }

  theorem instantiation_meta(x : Variable, phi : Formula, t : Term,
      phi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require full_substitution(t($x), $phi, $t, $phi_0);

    assume any($x, $phi);

    infer $phi_0;

    step instantiation($x, $phi, $t, $phi_0);
    step modus_ponens(any($x, $phi), $phi_0);
  }

  theorem implication_substitution(x : Variable, t : Term,
      phi : Formula, psi : Formula, phi_0 : Formula, psi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require free_for($t, t($x), $psi);
    require full_substitution(t($x), $phi, $t, $phi_0);
    require full_substitution(t($x), $psi, $t, $psi_0);

    assume implies($phi, $psi);

    infer implies($phi_0, $psi_0);

    step generalization($x, implies($phi, $psi));
    step instantiation($x, implies($phi, $psi), $t, implies($phi_0, $psi_0));
    step modus_ponens(any($x, implies($phi, $psi)), implies($phi_0, $psi_0));
  }

  theorem negation_substitution(x : Variable, t : Term,
      phi : Formula, phi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require full_substitution(t($x), $phi, $t, $phi_0);

    assume not($phi);

    infer not($phi_0);

    step generalization($x, not($phi));
    step instantiation($x, not($phi), $t, not($phi_0));
    step modus_ponens(any($x, not($phi)), not($phi_0));
  }

  theorem conjunction_substitution(x : Variable, t : Term,
      phi : Formula, psi : Formula, phi_0 : Formula, psi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require free_for($t, t($x), $psi);
    require full_substitution(t($x), $phi, $t, $phi_0);
    require full_substitution(t($x), $psi, $t, $psi_0);

    assume and($phi, $psi);

    infer and($phi_0, $psi_0);

    step generalization($x, and($phi, $psi));
    step instantiation($x, and($phi, $psi), $t, and($phi_0, $psi_0));
    step modus_ponens(any($x, and($phi, $psi)), and($phi_0, $psi_0));
  }

  theorem disjunction_substitution(x : Variable, t : Term,
      phi : Formula, psi : Formula, phi_0 : Formula, psi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require free_for($t, t($x), $psi);
    require full_substitution(t($x), $phi, $t, $phi_0);
    require full_substitution(t($x), $psi, $t, $psi_0);

    assume or($phi, $psi);

    infer or($phi_0, $psi_0);

    step generalization($x, or($phi, $psi));
    step instantiation($x, or($phi, $psi), $t, or($phi_0, $psi_0));
    step modus_ponens(any($x, or($phi, $psi)), or($phi_0, $psi_0));
  }

  theorem biconditional_substitution(x : Variable, t : Term,
      phi : Formula, psi : Formula, phi_0 : Formula, psi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require free_for($t, t($x), $psi);
    require full_substitution(t($x), $phi, $t, $phi_0);
    require full_substitution(t($x), $psi, $t, $psi_0);

    assume iff($phi, $psi);

    infer iff($phi_0, $psi_0);

    step generalization($x, iff($phi, $psi));
    step instantiation($x, iff($phi, $psi), $t, iff($phi_0, $psi_0));
    step modus_ponens(any($x, iff($phi, $psi)), iff($phi_0, $psi_0));
  }

  theorem quantified_implication_meta(x : Variable, phi : Formula,
      psi : Formula) {
    assume implies($phi, $psi);

    infer implies(any($x, $phi), any($x, $psi));

    step generalization($x, implies($phi, $psi));
    step quantified_implication($x, $phi, $psi);
    step modus_ponens(any($x, implies($phi, $psi)),
        implies(any($x, $phi), any($x, $psi)));
  }

  theorem quantified_biconditional_meta(x : Variable, phi : Formula,
      psi : Formula) {
    assume iff($phi, $psi);

    infer iff(any($x, $phi), any($x, $psi));

    step biconditional_elimination_left_meta($phi, $psi);
    step biconditional_elimination_right_meta($phi, $psi);
    step quantified_implication_meta($x, $phi, $psi);
    step quantified_implication_meta($x, $psi, $phi);
    step biconditional_introduction_meta(any($x, $phi), any($x, $psi));
  }

  theorem instantiation_elimination(x : Variable, phi : Formula) {
    infer implies(any($x, $phi), $phi);

    step instantiation($x, $phi, t($x), $phi);
  }

  theorem instantiation_elimination_meta(x : Variable, phi : Formula) {
    assume any($x, $phi);

    infer $phi;

    step instantiation_elimination($x, $phi);
    step modus_ponens(any($x, $phi), $phi);
  }

  theorem implication_generalization(x : Variable, phi : Formula,
      psi : Formula) {
    assume implies($phi, $psi);

    infer implies(any($x, $phi), any($x, $psi));

    step generalization($x, implies($phi, $psi));
    step quantified_implication($x, $phi, $psi);
    step modus_ponens(any($x, implies($phi, $psi)),
        implies(any($x, $phi), any($x, $psi)));
  }

  theorem biconditional_generalization(x : Variable, phi : Formula,
      psi : Formula) {
    assume iff($phi, $psi);

    infer iff(any($x, $phi), any($x, $psi));

    step biconditional_elimination_meta($phi, $psi);
    step implication_generalization($x, $phi, $psi);
    step implication_generalization($x, $psi, $phi);
    step biconditional_introduction_meta(any($x, $phi), any($x, $psi));
  }

  theorem quantified_conjunction(x : Variable, phi : Formula,
      psi : Formula) {
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
  theorem quantified_conjunction_implication_meta(x : Variable, phi : Formula,
      psi : Formula, chi : Formula) {
    assume implies(and($phi, $psi), $chi);

    infer implies(and(any($x, $phi), any($x, $psi)), any($x, $chi));

    step quantified_implication_meta($x, and($phi, $psi), $chi);
    step quantified_conjunction($x, $phi, $psi);
    step hypothetical_syllogism_meta(and(any($x, $phi), any($x, $psi)),
        any($x, and($phi, $psi)), any($x, $chi));
  }

  expr Formula eq(s : Term, t : Term) {
    latex $s + " = " + $t;
  }

  axiom equality_reflexive_v(x : Variable) {
    infer any($x, eq(t($x), t($x)));
  }

  axiom equality_substitution(x : Variable, phi : Formula, y : Variable,
      phi_0 : Formula) {
    require free_for(t($y), t($x), $phi);
    require substitution(t($x), $phi, t($y), $phi_0);

    infer implies(eq(t($x), t($y)), implies($phi, $phi_0));
  }

  theorem equality_substitution_2(x : Variable, phi : Formula, y : Variable,
      phi_0 : Formula) {
    require free_for(t($y), t($x), $phi);
    require substitution(t($x), $phi, t($y), $phi_0);

    infer implies($phi, implies(eq(t($x), t($y)), $phi_0));

    step equality_substitution($x, $phi, $y, $phi_0);
    step implication_commutation(eq(t($x), t($y)), $phi, $phi_0);
    step modus_ponens(implies(eq(t($x), t($y)), implies($phi, $phi_0)),
        implies($phi, implies(eq(t($x), t($y)), $phi_0)));
  }

  namespace lemma {
    theorem equality_symmetric_l1(x : Variable, y : Variable) {
      infer implies(eq(t($x), t($y)), eq(t($y), t($x)));

      step equality_reflexive_v($x);
      step instantiation_elimination($x, eq(t($x), t($x)));
      step modus_ponens(any($x, eq(t($x), t($x))), eq(t($x), t($x)));
      step equality_substitution($x, eq(t($x), t($x)), $y, eq(t($y), t($x)));
      step intermediate_elimination(eq(t($x), t($y)),
          eq(t($x), t($x)), eq(t($y), t($x)));
    }
  }

  theorem equality_symmetric(x : Variable, y : Variable) {
    infer any($x, any($y,
        iff(eq(t($x), t($y)), eq(t($y), t($x)))));

    step lemma.equality_symmetric_l1($x, $y);
    step lemma.equality_symmetric_l1($y, $x);
    step biconditional_introduction_meta(eq(t($x), t($y)),
        eq(t($y), t($x)));
    step generalization($y,
        iff(eq(t($x), t($y)), eq(t($y), t($x))));
    step generalization($x, any($y,
        iff(eq(t($x), t($y)), eq(t($y), t($x)))));
  }

  theorem equality_substitution_reversed(x : Variable, phi : Formula,
      y : Variable, phi_0 : Formula) {
    require free_for(t($y), t($x), $phi);
    require substitution(t($x), $phi, t($y), $phi_0);

    infer implies(eq(t($y), t($x)), implies($phi, $phi_0));

    step equality_symmetric($x, $y);
    step instantiation_elimination_meta($x,
        any($y, iff(eq(t($x), t($y)), eq(t($y), t($x)))));
    step instantiation_elimination_meta($y,
        iff(eq(t($x), t($y)), eq(t($y), t($x))));
    step biconditional_elimination_left_meta(eq(t($x), t($y)),
        eq(t($y), t($x)));
    step equality_substitution($x, $phi, $y, $phi_0);
    step hypothetical_syllogism_meta(eq(t($y), t($x)), eq(t($x), t($y)),
        implies($phi, $phi_0));
  }

  theorem equality_substitution_reversed_2(x : Variable, phi : Formula,
      y : Variable, phi_0 : Formula) {
    require free_for(t($y), t($x), $phi);
    require substitution(t($x), $phi, t($y), $phi_0);

    infer implies($phi, implies(eq(t($y), t($x)), $phi_0));

    step equality_substitution_reversed($x, $phi, $y, $phi_0);
    step implication_commutation(eq(t($y), t($x)), $phi, $phi_0);
    step modus_ponens(implies(eq(t($y), t($x)), implies($phi, $phi_0)),
        implies($phi, implies(eq(t($y), t($x)), $phi_0)));
  }

  theorem equality_transitive(x : Variable, y : Variable, z : Variable) {
    def transitive implies(eq(t($x), t($y)), implies(eq(t($y),
        t($z)), eq(t($x), t($z))));

    infer any($x, any($y, any($z,
        implies(eq(t($x), t($y)), implies(eq(t($y), t($z)),
        eq(t($x), t($z)))))));

    step equality_symmetric($x, $y);
    step instantiation_elimination($x, any($y,
        iff(eq(t($x), t($y)), eq(t($y), t($x)))));
    step modus_ponens(any($x, any($y,
        iff(eq(t($x), t($y)), eq(t($y), t($x))))),
        any($y, iff(eq(t($x), t($y)), eq(t($y), t($x)))));
    step instantiation_elimination($y,
        iff(eq(t($x), t($y)), eq(t($y), t($x))));
    step modus_ponens(any($y, iff(eq(t($x), t($y)),
        eq(t($y), t($x)))),
        iff(eq(t($x), t($y)), eq(t($y), t($x))));
    step equality_substitution($y, eq(t($y), t($z)),
        $x, eq(t($x), t($z)));
    step biconditional_elimination_right_meta(eq(t($x), t($y)),
        eq(t($y), t($x)));
    step hypothetical_syllogism_meta(eq(t($x), t($y)),
        eq(t($y), t($x)),
        implies(eq(t($y), t($z)), eq(t($x), t($z))));
    step generalization($z, %transitive);
    step generalization($y, any($z, %transitive));
    step generalization($x, any($y, any($z, %transitive)));
  }

  theorem instantiation_equality(x : Variable, y : Variable, z : Variable) {
    infer implies(any($z, implies(eq(t($z), t($x)), eq(t($z), t($y)))),
        eq(t($x), t($y)));
    /*infer implies(any($z, iff(eq(t($z), t($x)), eq(t($z), t($y)))),
        eq(t($x), t($y)));*/

    step instantiation($z, implies(eq(t($z), t($x)), eq(t($z), t($y))),
        t($x), implies(eq(t($x), t($x)), eq(t($x), t($y))));
    step equality_reflexive_v($x);
    step instantiation_elimination_meta($x, eq(t($x), t($x)));
    step intermediate_elimination(any($z, implies(eq(t($z), t($x)),
        eq(t($z), t($y)))), eq(t($x), t($x)), eq(t($x), t($y)));
  }

  expr Formula exists(x : Variable, phi : Formula) {
    latex "\\exists " + $x + " " + $phi;
    bind $x;
  }

  axiom existential_quantification(x : Variable, phi : Formula) {
    infer iff(exists($x, $phi), not(any($x, not($phi))));
  }

  theorem generalization_existential(x : Variable, phi : Formula, t : Term,
      phi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require full_substitution(t($x), $phi, $t, $phi_0);

    infer implies($phi_0, exists($x, $phi));

    step instantiation($x, not($phi), $t, not($phi_0));
    step transposition_4(any($x, not($phi)), $phi_0);
    step modus_ponens(implies(any($x, not($phi)), not($phi_0)),
        implies($phi_0, not(any($x, not($phi)))));
    step existential_quantification($x, $phi);
    step biconditional_elimination_left_meta(exists($x, $phi),
        not(any($x, not($phi))));
    step hypothetical_syllogism_meta($phi_0, not(any($x, not($phi))),
        exists($x, $phi));
  }

  theorem generalization_existential_meta(x : Variable, phi : Formula,
      t : Term, phi_0 : Formula) {
    require free_for($t, t($x), $phi);
    require full_substitution(t($x), $phi, $t, $phi_0);

    assume $phi_0;

    infer exists($x, $phi);

    step generalization_existential($x, $phi, $t, $phi_0);
    step modus_ponens($phi_0, exists($x, $phi));
  }

  theorem equality_existence(x : Variable, y : Variable) {
    infer any($x, exists($y, eq(t($x), t($y))));
    infer any($x, exists($y, eq(t($y), t($x))));

    step equality_reflexive_v($x);
    step instantiation_elimination_meta($x, eq(t($x), t($x)));
    step generalization_existential_meta($y, eq(t($x), t($y)), t($x),
        eq(t($x), t($x)));
    step generalization($x, exists($y, eq(t($x), t($y))));
    step generalization_existential_meta($y, eq(t($y), t($x)), t($x),
        eq(t($x), t($x)));
    step generalization($x, exists($y, eq(t($y), t($x))));
  }

  theorem implication_generalization_existential(x : Variable, phi : Formula,
      psi : Formula) {
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

  theorem biconditional_generalization_existential(x : Variable, phi : Formula,
      psi : Formula) {
    assume iff($phi, $psi);

    infer iff(exists($x, $phi), exists($x, $psi));

    step biconditional_elimination_left_meta($phi, $psi);
    step biconditional_elimination_right_meta($phi, $psi);
    step implication_generalization_existential($x, $phi, $psi);
    step implication_generalization_existential($x, $psi, $phi);
    step biconditional_introduction_meta(exists($x, $phi), exists($x, $psi));
  }

  expr Formula exists_unique(x : Variable, phi : Formula) {
    latex "\\exists! " + $x + " " + $phi;
    bind $x;
  }

  axiom existential_uniqueness(x : Variable, phi : Formula,
      y : Variable, phi_0 : Formula) {
    require distinct($x, $y);
    require free_for(t($y), t($x), $phi);
    require full_substitution(t($x), $phi, t($y), $phi_0);

    infer iff(exists_unique($x, $phi), and(exists($x, $phi),
        any($x, any($y, implies(and($phi, $phi_0), eq(t($x), t($y)))))));
  }

  theorem existential_uniqueness_biconditional(x : Variable, y : Variable,
      phi : Formula, psi : Formula, phi_0 : Formula, psi_0 : Formula) {
    require distinct($x, $y);
    require free_for(t($y), t($x), $phi);
    require full_substitution(t($x), $phi, t($y), $phi_0);
    require free_for(t($y), t($x), $psi);
    require full_substitution(t($x), $psi, t($y), $psi_0);

    assume iff($phi, $psi);

    infer iff(exists_unique($x, $phi), exists_unique($x, $psi));

    step biconditional_generalization_existential($x, $phi, $psi);
    step existential_uniqueness($x, $phi, $y, $phi_0);
    step existential_uniqueness($x, $psi, $y, $psi_0);
    step biconditional_substitution($x, t($y), $phi, $psi, $phi_0, $psi_0);
    step conjunction_biconditional_distribution_meta($phi, $psi, $phi_0,
        $psi_0);
    step biconditional_distribution_left_2(and($phi, $phi_0),
        and($psi, $psi_0), eq(t($x), t($y)));
    step modus_ponens(iff(and($phi, $phi_0), and($psi, $psi_0)),
        iff(implies(and($phi, $phi_0), eq(t($x), t($y))),
        implies(and($psi, $psi_0), eq(t($x), t($y)))));
    step biconditional_generalization($y, implies(and($phi, $phi_0),
        eq(t($x), t($y))), implies(and($psi, $psi_0), eq(t($x), t($y))));
    step biconditional_generalization($x, any($y, implies(and($phi, $phi_0),
        eq(t($x), t($y)))), any($y, implies(and($psi, $psi_0),
        eq(t($x), t($y)))));
    step conjunction_biconditional_distribution_meta(exists($x, $phi),
        exists($x, $psi), any($x, any($y, implies(and($phi, $phi_0),
        eq(t($x), t($y))))), any($x, any($y, implies(and($psi, $psi_0),
        eq(t($x), t($y))))));
    step biconditional_transitive_meta(exists_unique($x, $phi),
        and(exists($x, $phi), any($x, any($y, implies(and($phi, $phi_0),
        eq(t($x), t($y)))))),
        and(exists($x, $psi), any($x, any($y, implies(and($psi, $psi_0),
        eq(t($x), t($y)))))));
    step biconditional_transitive_meta_2(exists_unique($x, $phi),
        and(exists($x, $psi), any($x, any($y, implies(and($psi, $psi_0),
        eq(t($x), t($y)))))),
        exists_unique($x, $psi));
  }

  theorem equality_existence_uniqueness(x : Variable, y : Variable) {
    require distinct($x, $y);

    def x @dummy(Variable);
    def y @dummy(Variable);
    def z @dummy(Variable);

    infer any($x, exists_unique($y, eq(t($x), t($y))));
    infer any($x, exists_unique($y, eq(t($y), t($x))));

    step equality_existence($x, $y);
    step instantiation_meta($x, exists($y, eq(t($x), t($y))),
        t($x), exists($y, eq(t($x), t($y))));
    step equality_transitive(%x, %y, %z);
    step instantiation_meta(%x,
        any(%y, any(%z, implies(eq(t(%x),
        t(%y)), implies(eq(t(%y), t(%z)),
        eq(t(%x), t(%z)))))),
        t($y),
        any(%y, any(%z, implies(eq(t($y),
        t(%y)), implies(eq(t(%y), t(%z)),
        eq(t($y), t(%z)))))));
    step instantiation_meta(%y,
        any(%z, implies(eq(t($y), t(%y)),
        implies(eq(t(%y), t(%z)),
        eq(t($y), t(%z))))), t($x),
        any(%z, implies(eq(t($y), t($x)),
        implies(eq(t($x), t(%z)), eq(t($y), t(%z))))));
    step instantiation_meta(%z,
        implies(eq(t($y), t($x)),
        implies(eq(t($x), t(%z)), eq(t($y), t(%z)))),
        t(%z), implies(eq(t($y), t($x)),
        implies(eq(t($x), t(%z)), eq(t($y), t(%z)))));
    step equality_symmetric(%x, %y);
    step instantiation_meta(%x, any(%y,
        iff(eq(t(%x), t(%y)),
        eq(t(%y), t(%x)))), t($x),
        any(%y, iff(eq(t($x), t(%y)),
        eq(t(%y), t($x)))));
    step instantiation_meta(%y,
        iff(eq(t($x), t(%y)), eq(t(%y), t($x))),
        t($y), iff(eq(t($x), t($y)), eq(t($y), t($x))));
    step biconditional_elimination_right_meta(eq(t($x), t($y)),
        eq(t($y), t($x)));
    step hypothetical_syllogism_meta(eq(t($x), t($y)), eq(t($y), t($x)),
        implies(eq(t($x), t(%z)), eq(t($y), t(%z))));
    step hypothetical_implication_to_conjunction(eq(t($x), t($y)),
        eq(t($x), t(%z)), eq(t($y), t(%z)));
    step modus_ponens(implies(eq(t($x), t($y)),
        implies(eq(t($x), t(%z)), eq(t($y), t(%z)))),
        implies(and(eq(t($x), t($y)), eq(t($x), t(%z))),
        eq(t($y), t(%z))));
    step generalization(%z, implies(and(eq(t($x), t($y)),
        eq(t($x), t(%z))), eq(t($y), t(%z))));
    step generalization($y, any(%z, implies(and(eq(t($x), t($y)),
        eq(t($x), t(%z))), eq(t($y), t(%z)))));
    step conjunction_introduction_meta(exists($y, eq(t($x), t($y))),
        any($y, any(%z, implies(and(eq(t($x), t($y)),
        eq(t($x), t(%z))), eq(t($y), t(%z))))));
    step existential_uniqueness($y, eq(t($x), t($y)), %z,
        eq(t($x), t(%z)));
    step biconditional_elimination_left_meta(exists_unique($y,
        eq(t($x), t($y))), and(exists($y, eq(t($x), t($y))),
        any($y, any(%z, implies(and(eq(t($x), t($y)),
        eq(t($x), t(%z))), eq(t($y), t(%z)))))));
    step modus_ponens(and(exists($y, eq(t($x), t($y))),
        any($y, any(%z, implies(and(eq(t($x), t($y)),
        eq(t($x), t(%z))), eq(t($y), t(%z)))))),
        exists_unique($y, eq(t($x), t($y))));
    step existential_uniqueness_biconditional($y, %z,
        eq(t($x), t($y)), eq(t($y), t($x)),
        eq(t($x), t(%z)), eq(t(%z), t($x)));
    step biconditional_elimination_right_meta(
        exists_unique($y, eq(t($x), t($y))),
        exists_unique($y, eq(t($y), t($x))));
    step modus_ponens(exists_unique($y, eq(t($x), t($y))),
        exists_unique($y, eq(t($y), t($x))));
    step generalization($x, exists_unique($y, eq(t($x), t($y))));
    step generalization($x, exists_unique($y, eq(t($y), t($x))));
  }

  type Predicate1 atomic;
  type Predicate2 atomic;
  type Predicate3 atomic;

  expr Formula eval_p1(p : Predicate1, t_1 : Term) {
    latex "\\left( " + $p + " \\right)\\left( " + $t_1 + " \\right) ";
  }

  expr Formula eval_p2(p : Predicate2, t_1 : Term, t_2 : Term) {
    latex "\\left( " + $p + " \\right)\\left( " + $t_1 + " , " + $t_2 +
        " \\right) ";
  }

  expr Formula eval_p3(p : Predicate3, t_1 : Term, t_2 : Term, t_3 : Term) {
    latex "\\left( " + $p + " \\right)\\left( " + $t_1 + " , " + $t_2 +
        " , " + $t_3 + " \\right) ";
  }

  type Function0 atomic;
  type Function1 atomic;
  type Function2 atomic;
  type Function3 atomic;

  expr Term eval_f0(f : Function0) {
    latex $f;
  }

  expr Term eval_f1(f : Function1, t_1 : Term) {
    latex "\\left( " + $f + " \\right)\\left( " + $t_1 + " \\right) ";
  }

  expr Term eval_f2(f : Function2, t_1 : Term, t_2 : Term) {
    latex "\\left( " + $f + " \\right)\\left( " + $t_1 + " , " + $t_2 +
        " \\right) ";
  }

  expr Term eval_f3(f : Function3, t_1 : Term, t_2 : Term, t_3 : Term) {
    latex "\\left( " + $f + " \\right)\\left( " + $t_1 + " , " + $t_2 +
        " , " + $t_3 + " \\right) ";
  }

  axiom extend_predicate1(p : Predicate1, phi : Formula, x_1 : Variable) {
    require cover_free($x_1, $phi);
    require unused($p);

    infer any($x_1, iff(eval_p1($p, t($x_1)), $phi));
  }

  axiom extend_predicate2(p : Predicate2, phi : Formula, x_1 : Variable,
      x_2 : Variable) {
    require distinct($x_1, $x_2);
    require cover_free($x_1, $x_2, $phi);
    require unused($p);

    infer any($x_1, any($x_2, iff(eval_p2($p, t($x_1), t($x_2)), $phi)));
  }

  axiom extend_predicate3(p : Predicate3, phi : Formula, x_1 : Variable,
      x_2 : Variable, x_3 : Variable) {
    require distinct($x_1, $x_2, $x_3);
    require cover_free($x_1, $x_2, $x_3, $phi);
    require unused($p);

    infer any($x_1, any($x_2, any($x_3,
        iff(eval_p3($p, t($x_1), t($x_2), t($x_3)), $phi))));
  }

  axiom extend_function0(f : Function0, y : Variable, phi : Formula,
      phi_0 : Formula) {
    require free_for(eval_f0($f), t($y), $phi);
    require full_substitution(t($y), $phi, eval_f0($f), $phi_0);
    require unused($f);

    assume exists_unique($y, $phi);

    infer $phi_0;
  }

  theorem extend_term_function0(f : Function0, t : Term) {
    require unused($f);

    def x @dummy(Variable);
    def y @dummy(Variable);

    infer eq(eval_f0($f), $t);

    step equality_existence_uniqueness(%x, %y);
    step instantiation_meta(%x, exists_unique(%y,
        eq(t(%y), t(%x))), $t,
        exists_unique(%y, eq(t(%y), $t)));
    step extend_function0($f, %y,
        eq(t(%y), $t),
        eq(eval_f0($f), $t));
  }

  axiom extend_function1(f : Function1, y : Variable, phi : Formula,
      phi_0 : Formula, x_1 : Variable) {
    require distinct($y, $x_1);
    require cover_free($y, $x_1, $phi);
    require free_for(eval_f1($f, t($x_1)), t($y), $phi);
    require full_substitution(t($y), $phi, eval_f1($f, t($x_1)), $phi_0);
    require unused($f);

    assume any($x_1, exists_unique($y, $phi));

    infer any($x_1, $phi_0);
  }

  theorem extend_term_function1(f : Function1, t : Term, x_1 : Variable) {
    def x @dummy(Variable);
    def y @dummy(Variable);

    require unused($f);
    require cover_free(%y, $x_1, eq(t(%y), $t));

    infer any($x_1, eq(eval_f1($f, t($x_1)), $t));

    step equality_existence_uniqueness(%x, %y);
    step instantiation_meta(%x, exists_unique(%y,
        eq(t(%y), t(%x))), $t,
        exists_unique(%y, eq(t(%y), $t)));
    step generalization($x_1, exists_unique(%y, eq(t(%y), $t)));
    step extend_function1($f, %y,
        eq(t(%y), $t), eq(eval_f1($f, t($x_1)), $t), $x_1);
  }

  axiom extend_function2(f : Function2, y : Variable, phi : Formula,
      phi_0 : Formula, x_1 : Variable, x_2 : Variable) {
    require distinct($y, $x_1, $x_2);
    require cover_free($y, $x_1, $x_2, $phi);
    require free_for(eval_f2($f, t($x_1), t($x_2)), t($y), $phi);
    require full_substitution(t($y), $phi,
        eval_f2($f, t($x_1), t($x_2)), $phi_0);
    require unused($f);

    assume any($x_1, any($x_2, exists_unique($y, $phi)));

    infer any($x_1, any($x_2, $phi_0));
  }

  theorem extend_term_function2(f : Function2, t : Term, x_1 : Variable,
      x_2 : Variable) {
    def x @dummy(Variable);
    def y @dummy(Variable);

    require unused($f);
    require distinct($x_1, $x_2);
    require cover_free(%y, $x_1, $x_2, eq(t(%y), $t));

    infer any($x_1, any($x_2, eq(eval_f2($f, t($x_1), t($x_2)), $t)));

    step equality_existence_uniqueness(%x, %y);
    step instantiation_meta(%x, exists_unique(%y,
        eq(t(%y), t(%x))), $t,
        exists_unique(%y, eq(t(%y), $t)));
    step generalization($x_2,
        exists_unique(%y, eq(t(%y), $t)));
    step generalization($x_1, any($x_2,
        exists_unique(%y, eq(t(%y), $t))));
    step extend_function2($f, %y,
        eq(t(%y), $t), eq(eval_f2($f, t($x_1), t($x_2)), $t),
        $x_1, $x_2);
  }

  axiom extend_function3(f : Function3, y : Variable, phi : Formula,
      phi_0 : Formula, x_1 : Variable, x_2 : Variable, x_3 : Variable) {
    require distinct($y, $x_1, $x_2, $x_3);
    require cover_free($y, $x_1, $x_2, $x_3, $phi);
    require free_for(eval_f3($f, t($x_1), t($x_2), t($x_3)), t($y), $phi);
    require full_substitution(t($y), $phi,
        eval_f3($f, t($x_1), t($x_2), t($x_3)), $phi_0);
    require unused($f);

    assume any($x_1, any($x_2, any($x_3, exists_unique($y, $phi))));

    infer any($x_1, any($x_2, any($x_3, $phi_0)));
  }

  theorem extend_term_function3(f : Function3, t : Term, x_1 : Variable,
      x_2 : Variable, x_3 : Variable) {
    def x @dummy(Variable);
    def y @dummy(Variable);

    require unused($f);
    require distinct($x_1, $x_2, $x_3);
    require cover_free(%y, $x_1, $x_2, $x_3, eq(t(%y), $t));

    infer any($x_1, any($x_2, any($x_3,
        eq(eval_f3($f, t($x_1), t($x_2), t($x_3)), $t))));

    step equality_existence_uniqueness(%x, %y);
    step instantiation_meta(%x, exists_unique(%y,
        eq(t(%y), t(%x))), $t,
        exists_unique(%y, eq(t(%y), $t)));
    step generalization($x_3,
        exists_unique(%y, eq(t(%y), $t)));
    step generalization($x_2, any($x_3,
        exists_unique(%y, eq(t(%y), $t))));
    step generalization($x_1, any($x_2, any($x_3,
        exists_unique(%y, eq(t(%y), $t)))));
    step extend_function3($f, %y,
        eq(t(%y), $t),
        eq(eval_f3($f, t($x_1), t($x_2), t($x_3)), $t),
        $x_1, $x_2, $x_3);
  }
}
