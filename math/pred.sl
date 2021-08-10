/*

First Order Logic (with Equality):

Define terms, variables, and quantification. After developing the rules
for free and bound variables, add the axioms for first order logic with
equality. The axioms are taken from Mendelson, pgs. 69-70 and 95.

*/
import "prop.sl";
namespace predicate_calculus
{
  use propositional_calculus;

  type Term;
  type Variable atomic binds;

  constspace vars Variable;

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
  quantified_biconditional_meta(x : Variable, phi : Formula, psi : Formula)
  {
    assume iff($phi, $psi);

    infer iff(any($x, $phi), any($x, $psi));

    step biconditional_elimination_left_meta($phi, $psi);
    step biconditional_elimination_right_meta($phi, $psi);
    step quantified_implication_meta($x, $phi, $psi);
    step quantified_implication_meta($x, $psi, $phi);
    step biconditional_introduction_meta(any($x, $phi), any($x, $psi));
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

  theorem
  biconditional_generalization_existential(x : Variable, phi : Formula,
    psi : Formula)
  {
    assume iff($phi, $psi);

    infer iff(exists($x, $phi), exists($x, $psi));

    step biconditional_elimination_left_meta($phi, $psi);
    step biconditional_elimination_right_meta($phi, $psi);
    step implication_generalization_existential($x, $phi, $psi);
    step implication_generalization_existential($x, $psi, $phi);
    step biconditional_introduction_meta(exists($x, $phi), exists($x, $psi));
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
      any($x, any($y, implies(and($phi, $phi_0), eq(t($x), t($y)))))));
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
