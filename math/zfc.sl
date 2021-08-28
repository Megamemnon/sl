import "prop.sl";
import "pred.sl";
namespace zfc {
  use propositional_calculus;
  use predicate_calculus;

  const in : Predicate2 {
    latex "\\in";
  }

  axiom extensionality(x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    infer any($x, any($y, implies(
        any($z, iff(eval_p2(in, t($z), t($x)),
        eval_p2(in, t($z), t($y)))), eq(t($x), t($y)))));
  }

  theorem equivalent_set_membership_condition(phi : Formula,
      x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    infer any($x, any($y, implies(and(
        any($z, iff(eval_p2(in, t($z), t($x)), $phi)),
        any($z, iff(eval_p2(in, t($z), t($y)), $phi))),
        eq(t($x), t($y)))));

    step extensionality($x, $y, $z);
    step instantiation_elimination_meta($x,
        any($y, implies(
        any($z, iff(eval_p2(in, t($z), t($x)),
        eval_p2(in, t($z), t($y)))), eq(t($x), t($y)))));
    step instantiation_elimination_meta($y,
        implies(any($z, iff(eval_p2(in, t($z), t($x)),
        eval_p2(in, t($z), t($y)))), eq(t($x), t($y))));
    step conjunction_biconditional_elimination($phi,
        eval_p2(in, t($z), t($x)), eval_p2(in, t($z), t($y)));
    step quantified_conjunction_implication_meta($z,
        iff(eval_p2(in, t($z), t($x)), $phi),
        iff(eval_p2(in, t($z), t($y)), $phi),
        iff(eval_p2(in, t($z), t($x)),
        eval_p2(in, t($z), t($y))));
    step hypothetical_syllogism_meta(and(
        any($z, iff(eval_p2(in, t($z), t($x)), $phi)),
        any($z, iff(eval_p2(in, t($z), t($y)), $phi))),
        any($z, iff(eval_p2(in, t($z), t($x)),
        eval_p2(in, t($z), t($y)))), eq(t($x), t($y)));
    step generalization($y, implies(and(
        any($z, iff(eval_p2(in, t($z), t($x)), $phi)),
        any($z, iff(eval_p2(in, t($z), t($y)), $phi))),
        eq(t($x), t($y))));
    step generalization($x, any($y, implies(and(
        any($z, iff(eval_p2(in, t($z), t($x)), $phi)),
        any($z, iff(eval_p2(in, t($z), t($y)), $phi))),
        eq(t($x), t($y)))));
  }

  theorem set_membership_condition_unique(phi : Formula,
      x : Variable, z : Variable) {
    require distinct($x, $z);

    infer implies(exists($x, any($z, iff(eval_p2(in, t($z),
        t($x)), $phi))), exists_unique($x, any($z,
        iff(eval_p2(in, t($z), t($x)), $phi))));

    def y @dummy(Variable);
    def ex exists($x, any($z, iff(eval_p2(in, t($z), t($x)),
        $phi)));
    def uniq any($x, any(%y, implies(and(
        any($z, iff(eval_p2(in, t($z), t($x)), $phi)),
        any($z, iff(eval_p2(in, t($z), t(%y)), $phi))),
        eq(t($x), t(%y)))));

    step conjunction_introduction(%uniq, %ex);
    step conjunction_commutation(%uniq, %ex);
    step equivalent_set_membership_condition($phi, $x, %y, $z);
    step modus_ponens(%uniq, implies(%ex, and(%uniq, %ex)));
    step hypothetical_syllogism_meta(%ex, and(%uniq, %ex), and(%ex, %uniq));
    step existential_uniqueness($x, any($z, iff(
        eval_p2(in, t($z), t($x)), $phi)), %y,
        any($z, iff(eval_p2(in, t($z), t(%y)), $phi)));
    step biconditional_elimination_left_meta(exists_unique($x,
        any($z, iff(eval_p2(in, t($z), t($x)), $phi))),
        and(exists($x, any($z,
        iff(eval_p2(in, t($z), t($x)), $phi))),
        any($x, any(%y, implies(and(any($z,
        iff(eval_p2(in, t($z), t($x)), $phi)),
        any($z, iff(eval_p2(in, t($z), t(%y)), $phi))),
        eq(t($x), t(%y)))))));
    step hypothetical_syllogism_meta(%ex, and(%ex, %uniq),
        exists_unique($x, any($z, iff(eval_p2(in, t($z),
        t($x)), $phi))));
  }

  theorem set_membership_condition_unique_meta(phi : Formula,
      x : Variable, z : Variable) {
    require distinct($x, $z);

    assume exists($x, any($z, iff(eval_p2(in, t($z), t($x)), $phi)));

    infer exists_unique($x, any($z, iff(eval_p2(in, t($z), t($x)), $phi)));

    def y @dummy(Variable);

    step set_membership_condition_unique($phi, $x, $z);
    step modus_ponens(exists($x, any($z, iff(eval_p2(in, t($z), t($x)),
        $phi))), exists_unique($x, any($z, iff(eval_p2(in, t($z), t($x)),
        $phi))));
  }

  axiom regularity(x : Variable, y : Variable, z : Variable, a : Variable) {
    def nonempty exists($a, eval_p2(in, t($a), t($x)));

    infer any($x, implies(%nonempty,
        exists($y, and(eval_p2(in, t($y), t($x)),
        not(exists($z, and(eval_p2(in, t($z), t($y)),
        eval_p2(in, t($z), t($y)))))))));
  }

  axiom specification(phi : Formula, x : Variable, y : Variable,
      z : Variable) {
    require distinct($x, $y, $z);
    require cover_free($x, $z, $phi);

    infer any($z, exists($y, any($x,
        iff(eval_p2(in, t($x), t($y)),
        and(eval_p2(in, t($x), t($z)), $phi)))));
  }

  /* TODO: prove this from specification. */
  axiom set_extraction(phi : Formula, x : Variable, y : Variable) {
    require distinct($x, $y);

    assume exists($x, any($y, implies($phi, eval_p2(in, t($y), t($x)))));

    infer exists($x, any($y, iff(eval_p2(in, t($y), t($x)), $phi)));
  }

  theorem set_extraction_unique(phi : Formula, x : Variable, y : Variable) {
    require distinct($x, $y);

    assume exists($x, any($y, implies($phi, eval_p2(in, t($y), t($x)))));

    infer exists_unique($x, any($y, iff(eval_p2(in, t($y), t($x)), $phi)));

    step set_extraction($phi, $x, $y);
    step set_membership_condition_unique_meta($phi, $x, $y);
  }

  const empty : Function0 {
    latex "\\emptyset";
  }

  namespace lemma {
    theorem empty_set_exists(x : Variable, y : Variable) {
      require distinct($x, $y);

      def z @dummy(Variable);

      infer exists($y, any($x, not(eval_p2(in, t($x), t($y)))));

      step specification(F, $x, $y, %z);
      step false();
      step negative_conjunction_introduction(F, eval_p2(in, t($x), t(%z)));
      step modus_ponens(not(F), not(and(eval_p2(in, t($x), t(%z)), F)));
      step instantiation_elimination(%z, exists($y, any($x,
          iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t(%z)), F)))));
      step modus_ponens(any(%z, exists($y, any($x,
          iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t(%z)), F))))),
          exists($y, any($x,
          iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t(%z)), F)))));
      step identity(iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t(%z)), F)));
      step infer_negated_equivalent(iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t(%z)), F)),
          eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t(%z)), F));
      step implication_generalization($x, iff(eval_p2(in, t($x),
          t($y)), and(eval_p2(in, t($x), t(%z)), F)),
          not(eval_p2(in, t($x), t($y))));
      step implication_generalization_existential($y,
          any($x, iff(eval_p2(in, t($x),
          t($y)), and(eval_p2(in, t($x), t(%z)), F))),
          any($x, not(eval_p2(in, t($x), t($y)))));
      step modus_ponens(exists($y, any($x,
          iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t(%z)), F)))),
          exists($y, any($x, not(eval_p2(in, t($x), t($y))))));
    }

    theorem empty_set_unique(x : Variable, y : Variable) {
      require distinct($x, $y);

      infer exists_unique($y, any($x, not(eval_p2(in, t($x), t($y)))));

      def z @dummy(Variable);

      step empty_set_exists($x, $y);
      step biconditional_not_simplification(eval_p2(in, t($x), t($y)));
      step quantified_biconditional_meta($x, not(eval_p2(in, t($x), t($y))),
          iff(eval_p2(in, t($x), t($y)), F));
      step biconditional_generalization_existential($y,
          any($x, not(eval_p2(in, t($x), t($y)))),
          any($x, iff(eval_p2(in, t($x), t($y)), F)));
      step biconditional_elimination_right_meta(exists($y, any($x, not(
          eval_p2(in, t($x), t($y))))), exists($y, any($x, iff(eval_p2(in,
          t($x), t($y)), F))));
      step modus_ponens(exists($y, any($x, not(eval_p2(in, t($x), t($y))))),
          exists($y, any($x, iff(eval_p2(in, t($x), t($y)), F))));
      step set_membership_condition_unique(F, $y, $x);
      step modus_ponens(exists($y, any($x, iff(eval_p2(in, t($x), t($y)), F))),
          exists_unique($y, any($x, iff(eval_p2(in, t($x), t($y)), F))));
      step existential_uniqueness_biconditional($y, %z,
          any($x, not(eval_p2(in, t($x), t($y)))),
          any($x, iff(eval_p2(in, t($x), t($y)), F)),
          any($x, not(eval_p2(in, t($x), t(%z)))),
          any($x, iff(eval_p2(in, t($x), t(%z)), F)));
      step biconditional_elimination_left_meta(
          exists_unique($y, any($x, not(eval_p2(in, t($x), t($y))))),
          exists_unique($y, any($x, iff(eval_p2(in, t($x), t($y)), F))));
      step modus_ponens(
          exists_unique($y, any($x, iff(eval_p2(in, t($x), t($y)), F))),
          exists_unique($y, any($x, not(eval_p2(in, t($x), t($y))))));
    }
  }

  theorem empty_set(x : Variable) {
    infer any($x, not(eval_p2(in, t($x), eval_f0(empty))));

    def y @dummy(Variable);

    step lemma.empty_set_exists($x, %y);
    step lemma.empty_set_unique($x, %y);
    step extend_function0(empty, %y,
        any($x, not(eval_p2(in, t($x), t(%y)))),
        any($x, not(eval_p2(in, t($x), eval_f0(empty)))));
  }

  axiom pairing(x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    infer any($x, any($y, exists($z, and(
        eval_p2(in, t($x), t($z)),
        eval_p2(in, t($y), t($z))))));
  }

  namespace lemma {
    theorem unordered_pair_existence_uniqueness(x : Variable, y : Variable,
        z : Variable, w : Variable) {
      require distinct($x, $y, $z, $w);

      infer any($x, any($y, exists_unique($z, any($w,
          iff(eval_p2(in, t($w), t($z)), or(eq(t($w), t($x)),
          eq(t($w), t($y))))))));

      step pairing($x, $y, $z);
      step instantiation_elimination_meta($x,
          any($y, exists($z, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z))))));
      step instantiation_elimination_meta($y,
          exists($z, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z)))));
      step equality_substitution_reversed_2($x, eval_p2(in, t($x), t($z)),
          $w, eval_p2(in, t($w), t($z)));
      step equality_substitution_reversed_2($y, eval_p2(in, t($y), t($z)),
          $w, eval_p2(in, t($w), t($z)));
      step conjunction_elimination_left(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z)));
      step conjunction_elimination_right(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z)));
      step hypothetical_syllogism_meta(and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z))), eval_p2(in, t($x), t($z)),
          implies(eq(t($w), t($x)), eval_p2(in, t($w), t($z))));
      step hypothetical_syllogism_meta(and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z))), eval_p2(in, t($y), t($z)),
          implies(eq(t($w), t($y)), eval_p2(in, t($w), t($z))));
      step hypothetical_disjunction_elimination_meta(and(
          eval_p2(in, t($x), t($z)), eval_p2(in, t($y), t($z))),
          eval_p2(in, t($w), t($z)), eq(t($w), t($x)), eq(t($w), t($y)));
      step quantified_implication_meta($w, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z))), implies(or(eq(t($w), t($x)),
          eq(t($w), t($y))), eval_p2(in, t($w), t($z))));
      step bound_generalization($w, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z))));
      step hypothetical_syllogism_meta(and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z))), any($w, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z)))),
          any($w, implies(or(eq(t($w), t($x)), eq(t($w), t($y))),
          eval_p2(in, t($w), t($z)))));
      step implication_generalization_existential($z, and(
          eval_p2(in, t($x), t($z)), eval_p2(in, t($y), t($z))),
          any($w, implies(or(eq(t($w), t($x)), eq(t($w), t($y))),
          eval_p2(in, t($w), t($z)))));
      step modus_ponens(exists($z, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t($y), t($z)))),
          exists($z, any($w, implies(or(eq(t($w), t($x)), eq(t($w), t($y))),
          eval_p2(in, t($w), t($z))))));
      step set_extraction_unique(or(eq(t($w), t($x)), eq(t($w), t($y))),
          $z, $w);
      step generalization($y, exists_unique($z, any($w, iff(
          eval_p2(in, t($w), t($z)), or(eq(t($w), t($x)),
          eq(t($w), t($y)))))));
      step generalization($x, any($y, exists_unique($z, any($w, iff(
          eval_p2(in, t($w), t($z)), or(eq(t($w), t($x)),
          eq(t($w), t($y))))))));
    }
  }

  const pair : Function2 {
    latex "\\{ \\cdot_1 , \\cdot_2 \\}";
  }

  theorem pair_containing(x : Variable, y : Variable, w : Variable) {
    require distinct($x, $y, $w);

    def z @dummy(Variable);

    infer any($x, any($y, any($w, iff(eval_p2(in, t($w), eval_f2(pair,
        t($x), t($y))), or(eq(t($w), t($x)), eq(t($w), t($y)))))));

    step lemma.unordered_pair_existence_uniqueness($x, $y, %z, $w);
    step extend_function2(pair, %z, any($w, iff(
        eval_p2(in, t($w), t(%z)),
        or(eq(t($w), t($x)), eq(t($w), t($y))))),
        any($w, iff(eval_p2(in, t($w), eval_f2(pair, t($x), t($y))),
        or(eq(t($w), t($x)), eq(t($w), t($y))))), $x, $y);
  }

  namespace lemma {
    theorem singleton_existence_uniqueness(x : Variable,
        z : Variable, w : Variable) {
      require distinct($x, $z, $w);

      infer any($x, exists_unique($z, any($w, iff(eval_p2(in, t($w), t($z)),
          eq(t($w), t($x))))));

      step pairing($x, vars.dummyy, $z);
      step instantiation_elimination_meta($x,
          any(vars.dummyy, exists($z, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z))))));
      step instantiation_elimination_meta(vars.dummyy,
          exists($z, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z)))));
      step equality_substitution_reversed_2($x, eval_p2(in, t($x), t($z)),
          $w, eval_p2(in, t($w), t($z)));
      step conjunction_elimination_left(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z)));
      step hypothetical_syllogism_meta(and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z))), eval_p2(in, t($x), t($z)),
          implies(eq(t($w), t($x)), eval_p2(in, t($w), t($z))));
      step quantified_implication_meta($w, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z))), implies(eq(t($w), t($x)),
          eval_p2(in, t($w), t($z))));
      step bound_generalization($w, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z))));
      step hypothetical_syllogism_meta(and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z))), any($w,
          and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z)))),
          any($w, implies(eq(t($w), t($x)),
          eval_p2(in, t($w), t($z)))));
      step implication_generalization_existential($z, and(
          eval_p2(in, t($x), t($z)), eval_p2(in, t(vars.dummyy), t($z))),
          any($w, implies(eq(t($w), t($x)),
          eval_p2(in, t($w), t($z)))));
      step modus_ponens(exists($z, and(eval_p2(in, t($x), t($z)),
          eval_p2(in, t(vars.dummyy), t($z)))),
          exists($z, any($w, implies(eq(t($w), t($x)),
          eval_p2(in, t($w), t($z))))));
      step set_extraction_unique(eq(t($w), t($x)),
          $z, $w);
      step generalization($x, exists_unique($z, any($w, iff(
          eval_p2(in, t($w), t($z)), eq(t($w), t($x))))));
    }
  }

  const singleton : Function1 {
    latex "\\{ \\cdot_1 \\}";
  }

  theorem singleton_containing(x : Variable, w : Variable) {
    require distinct($x, $w);

    infer any($x, any($w, iff(eval_p2(in, t($w), eval_f1(singleton, t($x))),
        eq(t($w), t($x)))));

    def z @dummy(Variable);

    step lemma.singleton_existence_uniqueness($x, %z, $w);
    step extend_function1(singleton, %z, any($w, iff(
        eval_p2(in, t($w), t(%z)), eq(t($w), t($x)))),
        any($w, iff(eval_p2(in, t($w), eval_f1(singleton, t($x))),
        eq(t($w), t($x)))), $x);
  }

  namespace lemma {
    /* TODO: this should be a general theorem for terms. */
    theorem singleton_equality_1(x : Variable, y : Variable) {
      require distinct($x, $y);

      infer any($x, any($y, implies(eq(t($x), t($y)),
          eq(eval_f1(singleton, t($x)), eval_f1(singleton, t($y))))));

      step equality_substitution($x,
          eq(eval_f1(singleton, t($x)), eval_f1(singleton, t($x))),
          $y, eq(eval_f1(singleton, t($x)), eval_f1(singleton, t($y))));
      step equality_reflexive_v($x);
      step instantiation_meta($x, eq(t($x), t($x)),
          eval_f1(singleton, t($x)),
          eq(eval_f1(singleton, t($x)), eval_f1(singleton, t($x))));
      step intermediate_elimination(eq(t($x), t($y)),
          eq(eval_f1(singleton, t($x)), eval_f1(singleton, t($x))),
          eq(eval_f1(singleton, t($x)), eval_f1(singleton, t($y))));
      step generalization($y, implies(eq(t($x), t($y)),
          eq(eval_f1(singleton, t($x)), eval_f1(singleton, t($y)))));
      step generalization($x, any($y, implies(eq(t($x), t($y)),
          eq(eval_f1(singleton, t($x)), eval_f1(singleton, t($y))))));
    }
  }

  const ordered_pair : Function2 {
    latex "\\cdot_1 , \\cdot_2";
  }

  theorem ordered_pair_containing(x : Variable, y : Variable) {
    require distinct($x, $y);

    infer any($x, any($y, eq(eval_f2(ordered_pair, t($x), t($y)),
        eval_f2(pair, eval_f1(singleton, t($x)),
        eval_f2(pair, t($x), t($y))))));

    step extend_term_function2(ordered_pair,
        eval_f2(pair, eval_f1(singleton, t($x)), eval_f2(pair, t($x), t($y))),
        $x, $y);
  }

  axiom union(F : Variable, A : Variable, Y : Variable, x : Variable) {
    require distinct($F, $A, $Y, $x);

    infer any($F, exists($A, any($Y, any($x,
        implies(and(eval_p2(in, t($x), t($Y)), eval_p2(in, t($Y), t($F))),
        eval_p2(in, t($x), t($A)))))));
  }

  namespace lemma {
    theorem union_existence_uniqueness(F : Variable, A : Variable,
        Y : Variable, x : Variable) {
      require distinct($F, $A, $Y, $x);

      infer any($F, exists_unique($A, any($x, iff(eval_p2(in, t($x), t($A)),
          exists($Y, and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F))))))));

      step union($F, $A, $Y, $x);
      step instantiation_elimination_meta($F, exists($A, any($Y, any($x,
          implies(and(eval_p2(in, t($x), t($Y)), eval_p2(in, t($Y), t($F))),
          eval_p2(in, t($x), t($A)))))));
      step quantifier_commutation($Y, $x,
          implies(and(eval_p2(in, t($x), t($Y)), eval_p2(in, t($Y), t($F))),
          eval_p2(in, t($x), t($A))));
      step quantified_implication_mixed_despecialized($Y,
          and(eval_p2(in, t($x), t($Y)), eval_p2(in, t($Y), t($F))),
          eval_p2(in, t($x), t($A)));
      step implication_generalization($x,
          any($Y, implies(and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F))), eval_p2(in, t($x), t($A)))),
          implies(exists($Y, and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F)))), eval_p2(in, t($x), t($A))));
      step hypothetical_syllogism_meta(any($Y, any($x,
          implies(and(eval_p2(in, t($x), t($Y)), eval_p2(in, t($Y), t($F))),
          eval_p2(in, t($x), t($A))))),
          any($x, any($Y,
          implies(and(eval_p2(in, t($x), t($Y)), eval_p2(in, t($Y), t($F))),
          eval_p2(in, t($x), t($A))))),
          any($x, implies(exists($Y, and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F)))), eval_p2(in, t($x), t($A)))));
      step implication_generalization_existential($A,
          any($Y, any($x, implies(and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F))), eval_p2(in, t($x), t($A))))),
          any($x, implies(exists($Y, and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F)))), eval_p2(in, t($x), t($A)))));
      step modus_ponens(exists($A,
          any($Y, any($x, implies(and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F))), eval_p2(in, t($x), t($A)))))),
          exists($A, any($x, implies(exists($Y, and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F)))), eval_p2(in, t($x), t($A))))));
      step set_extraction_unique(exists($Y, and(eval_p2(in, t($x), t($Y)),
          eval_p2(in, t($Y), t($F)))), $A, $x);
      step generalization($F, exists_unique($A, any($x,
          iff(eval_p2(in, t($x), t($A)), exists($Y, and(
          eval_p2(in, t($x), t($Y)), eval_p2(in, t($Y), t($F))))))));
    }
  }

  const union_of : Function1 {
    latex "\\cup \\cdot_1";
  }

  theorem union_of_elements(x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    infer any($x, any($y, iff(eval_p2(in, t($y), eval_f1(union_of, t($x))),
        exists($z, and(eval_p2(in, t($y), t($z)),
        eval_p2(in, t($z), t($x)))))));

    def A @dummy(Variable);

    step lemma.union_existence_uniqueness($x, %A, $z, $y);
    step extend_function1(union_of, %A, any($y, iff(eval_p2(in, t($y), t(%A)),
        exists($z, and(eval_p2(in, t($y), t($z)),
        eval_p2(in, t($z), t($x)))))),
        any($y, iff(eval_p2(in, t($y), eval_f1(union_of, t($x))),
        exists($z, and(eval_p2(in, t($y), t($z)),
        eval_p2(in, t($z), t($x)))))), $x);
  }

  const union_of_pair : Function2 {
    latex "\\cdot_1 \\cup \\cdot_2";
  }

  theorem union_of_pair_def(x : Variable, y : Variable) {
    require distinct($x, $y);

    infer any($x, any($y, eq(eval_f2(union_of_pair, t($x), t($y)),
        eval_f1(union_of, eval_f2(pair, t($x), t($y))))));

    step extend_term_function2(union_of_pair,
        eval_f1(union_of, eval_f2(pair, t($x), t($y))), $x, $y);
  }

  const intersection_of : Function1 {
    latex "\\cap \\cdot";
  }

  /* TODO: Prove. */
  axiom intersection_of_elements(x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    infer any($x, any($y, iff(eval_p2(in, t($y),
        eval_f1(intersection_of, t($x))), any($z, implies(
        eval_p2(in, t($z), t($x)), eval_p2(in, t($y), t($z)))))));
  }

  const intersection_of_pair : Function2 {
    latex "\\cdot_1 \\cap \\cdot_2";
  }

  /* TODO: Prove. */
  axiom intersection_of_pair_def(x : Variable, y : Variable) {
    require distinct($x, $y);

    infer any($x, any($y, eq(eval_f2(intersection_of_pair, t($x), t($y)),
        eval_f1(intersection_of, eval_f2(pair, t($x), t($y))))));
  }

  axiom replacement(phi : Formula, x : Variable, y : Variable, A : Variable,
      B : Variable) {
    require cover_free($x, $y, $A, $phi);
    require not_free($B, $phi);

    infer any($A, implies(any($x, implies(eval_p2(in, t($x), t($A)),
        exists_unique($y, $phi))), exists($B, any($x, implies(
        eval_p2(in, t($x), t($A)), exists($y, and(
        eval_p2(in, t($y), t($B)), $phi)))))));
  }

  const successor : Function1 {
    latex "S";
  }

  theorem successor_of(x : Variable) {
    infer any($x, eq(eval_f1(successor, t($x)),
        eval_f2(union_of_pair, t($x), eval_f1(singleton, t($x)))));

    step extend_term_function1(successor,
        eval_f2(union_of_pair, t($x), eval_f1(singleton, t($x))), $x);
  }

  axiom infinity(X : Variable, y : Variable) {
    infer exists($X, and(eval_p2(in, eval_f0(empty), t($X)),
        any($y, implies(eval_p2(in, t($y), t($X)),
        eval_p2(in, eval_f1(successor, t($y)), t($X))))));
  }

  const subset : Predicate2 {
    latex "\\subset";
  }

  theorem subset_of(x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    infer any($x, any($y, iff(eval_p2(subset, t($x), t($y)),
        any($z, implies(eval_p2(in, t($z), t($x)),
        eval_p2(in, t($z), t($y)))))));

    step extend_predicate2(subset, any($z, implies(eval_p2(in, t($z), t($x)),
        eval_p2(in, t($z), t($y)))), $x, $y);
  }

  axiom power_set(x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    infer any($x, exists($y, any($z,
        implies(eval_p2(subset, t($z), t($x)), eval_p2(in, t($z), t($y))))));
  }

  namespace lemma {
    theorem power_set_existence_uniqueness(x : Variable, y : Variable,
        z : Variable) {
      require distinct($x, $y, $z);

      infer any($x, exists_unique($y, any($z,
          iff(eval_p2(in, t($z), t($y)), eval_p2(subset, t($z), t($x))))));

      step power_set($x, $y, $z);
      step instantiation_elimination_meta($x, exists($y, any($z,
          implies(eval_p2(subset, t($z), t($x)), eval_p2(in, t($z), t($y))))));
      step set_extraction_unique(eval_p2(subset, t($z), t($x)), $y, $z);
      step generalization($x, exists_unique($y, any($z,
          iff(eval_p2(in, t($z), t($y)), eval_p2(subset, t($z), t($x))))));
    }
  }

  const power_set_of : Function1 {
    latex "\\mathcal{P}";
  }

  theorem power_set_of_set(x : Variable, z : Variable) {
    require distinct($x, $z);

    infer any($x, any($z, iff(eval_p2(in, t($z), eval_f1(power_set_of, t($x))),
        eval_p2(subset, t($z), t($x)))));

    def y @dummy(Variable);

    step lemma.power_set_existence_uniqueness($x, %y, $z);
    step extend_function1(power_set_of, %y,
        any($z, iff(eval_p2(in, t($z), t(%y)),
        eval_p2(subset, t($z), t($x)))),
        any($z, iff(eval_p2(in, t($z), eval_f1(power_set_of, t($x))),
        eval_p2(subset, t($z), t($x)))), $x);
  }

  const cartesian_product : Function2 {
    latex "\\cdot_1 \\times \\cdot_2";
  }

  /* TODO: Prove. */
  axiom cartesian_product_of(X : Variable, Y : Variable, x : Variable,
      y : Variable, z : Variable) {
    require distinct($X, $Y, $x, $y, $z);

    infer any($X, any($Y, iff(eval_p2(in, t($z), eval_f2(cartesian_product,
        t($X), t($Y))), exists($x, exists($y, and(and(
        eval_p2(in, t($x), t($X)), eval_p2(in, t($y), t($Y))),
        eq(t($z), eval_f2(ordered_pair, t($x), t($y)))))))));
  }

  const map : Predicate3 {
    latex "\\cdot_1 : \\cdot_2 \\to \\cdot_3";
  }

  theorem map_of_sets(f : Variable, X : Variable, Y : Variable,
      x : Variable, y : Variable) {
    require distinct($f, $X, $Y, $x, $y);

    infer any($f, any($X, any($Y, iff(eval_p3(map, t($f), t($X), t($Y)),
        and(eval_p2(subset, t($f),
        eval_f2(cartesian_product, t($X), t($Y))), any($x,
        implies(eval_p2(in, t($x), t($X)), exists_unique($y,
        eval_p2(in, eval_f2(ordered_pair, t($x), t($y)), t($f))))))))));

    step extend_predicate3(map, and(eval_p2(subset, t($f),
        eval_f2(cartesian_product, t($X), t($Y))), any($x,
        implies(eval_p2(in, t($x), t($X)), exists_unique($y,
        eval_p2(in, eval_f2(ordered_pair, t($x), t($y)), t($f)))))),
        $f, $X, $Y);
  }

  const eval_map : Function2 {
    latex "\\cdot_1 \\left( \\cdot_2 \\right)";
  }

  const injective : Predicate3 {
    latex "\\cdot_1 : \\cdot_2 \\rightarrowtail \\cdot_3";
  }

  theorem injective_map(f : Variable, X : Variable, Y : Variable,
      x_1 : Variable, x_2 : Variable) {
    require distinct($f, $X, $Y, $x_1, $x_2);

    infer any($f, any($X, any($Y, iff(eval_p3(injective, t($f), t($X), t($Y)),
        and(eval_p3(map, t($f), t($X), t($Y)),
        any($x_1, any($x_2, implies(eq(eval_f2(eval_map, t($f), t($x_1)),
        eval_f2(eval_map, t($f), t($x_2))), eq(t($x_1), t($x_2))))))))));

    step extend_predicate3(injective, and(eval_p3(map, t($f), t($X), t($Y)),
        any($x_1, any($x_2, implies(eq(eval_f2(eval_map, t($f), t($x_1)),
        eval_f2(eval_map, t($f), t($x_2))), eq(t($x_1), t($x_2)))))),
        $f, $X, $Y);
  }

  const surjective : Predicate3 {
    latex "\\cdot_1 : \\cdot_2 \\twoheadrightarrow \\cdot_3";
  }

  theorem surjective_map(f : Variable, X : Variable, Y : Variable,
      x : Variable, y : Variable) {
    require distinct($f, $X, $Y, $x, $y);

    infer any($f, any($X, any($Y, iff(eval_p3(surjective, t($f), t($X), t($Y)),
        and(eval_p3(map, t($f), t($X), t($Y)),
        any($y, implies(eval_p2(in, t($y), t($Y)), exists($x,
        eq(eval_f2(eval_map, t($f), t($x)), t($y))))))))));

    step extend_predicate3(surjective, and(eval_p3(map, t($f), t($X), t($Y)),
        any($y, implies(eval_p2(in, t($y), t($Y)), exists($x,
        eq(eval_f2(eval_map, t($f), t($x)), t($y)))))), $f, $X, $Y);
  }

  const bijective : Predicate3 {
    latex "\\cdot_1 : \\cdot_2 \\to \\cdot_3";
  }

  theorem bijective_map(f : Variable, X : Variable, Y : Variable) {
    require distinct($f, $X, $Y);

    infer any($f, any($X, any($Y, iff(eval_p3(bijective, t($f), t($X), t($Y)),
        and(eval_p3(injective, t($f), t($X), t($Y)),
        eval_p3(surjective, t($f), t($X), t($Y)))))));

    step extend_predicate3(bijective,
        and(eval_p3(injective, t($f), t($X), t($Y)),
        eval_p3(surjective, t($f), t($X), t($Y))), $f, $X, $Y);
  }

  const naturals_ordinals : Function0 {
    latex "\\mathbb{N}";
  }

  const zero_ordinal : Function0 {
    latex "0";
  }

  /* TODO: Formulate the axiom of choice. */
}

namespace peano {
  use propositional_calculus;
  use predicate_calculus;
  use zfc;

  const peano_1 : Predicate2 {
    latex "\\mathrm{PA}_1";
  }

  theorem peano_zero(X : Variable, n_0 : Variable) {
    require distinct($X, $n_0);

    infer any($X, any($n_0, iff(eval_p2(peano_1, t($X), t($n_0)),
        eval_p2(in, t($n_0), t($X)))));

    step extend_predicate2(peano_1, eval_p2(in, t($n_0), t($X)),
        $X, $n_0);
  }

  const peano_2 : Predicate2 {
    latex "\\mathrm{PA}_2";
  }

  theorem peano_successor_injective(X : Variable, S : Variable) {
    require distinct($X, $S);

    infer any($X, any($S, iff(eval_p2(peano_2, t($X), t($S)),
        eval_p3(injective, t($S), t($X), t($X)))));

    step extend_predicate2(peano_2, eval_p3(injective, t($S), t($X), t($X)),
        $X, $S);
  }

  const peano_3 : Predicate3 {
    latex "\\mathrm{PA}_3";
  }

  theorem peano_no_zero_successor(X : Variable, n_0 : Variable, S : Variable,
      x : Variable) {
    require distinct($X, $n_0, $S, $x);

    infer any($X, any($n_0, any($S, iff(eval_p3(peano_3, t($X),
        t($n_0), t($S)), not(exists($x, eq(eval_f2(eval_map, t($S), t($x)),
        t($n_0))))))));

    step extend_predicate3(peano_3, not(exists($x,
        eq(eval_f2(eval_map, t($S), t($x)), t($n_0)))), $X, $n_0, $S);
  }

  const peano_model : Predicate3 {
    latex "\\mathrm{PA}";
  }

  theorem is_peano_model(X : Variable, n_0 : Variable, S : Variable) {
    require distinct($X, $n_0, $S);

    infer any($X, any($n_0, any($S, iff(eval_p3(peano_model,
        t($X), t($n_0), t($S)),
        and(eval_p2(peano_1, t($X), t($n_0)), and(
        eval_p2(peano_2, t($X), t($S)),
        eval_p3(peano_3, t($X), t($n_0), t($S))))))));

    step extend_predicate3(peano_model,
        and(eval_p2(peano_1, t($X), t($n_0)),
        and(eval_p2(peano_2, t($X), t($S)),
        eval_p3(peano_3, t($X), t($n_0), t($S)))),
        $X, $n_0, $S);
  }
}

namespace algebra {
  use propositional_calculus;
  use predicate_calculus;
  use zfc;

  const binary : Predicate2 {
    latex "\\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2";
  }

  theorem binary_operation() {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary, t(vars.f), t(vars.X)),
        eval_p3(map, t(vars.f), eval_f2(cartesian_product, t(vars.X),
        t(vars.X)), t(vars.X)))));

    step extend_predicate2(binary, eval_p3(map, t(vars.f),
        eval_f2(cartesian_product, t(vars.X), t(vars.X)), t(vars.X)),
        vars.f, vars.X);
  }

  const binary_commutative : Predicate2 {
    latex "\\mathrm{comm} \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem binary_operation_commutative() {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary_commutative, t(vars.f),
        t(vars.X)), and(eval_p2(binary, t(vars.f), t(vars.X)),
        any(vars.x, any(vars.y, implies(eval_p2(in,
        eval_f2(ordered_pair, t(vars.x), t(vars.y)),
        eval_f2(cartesian_product, t(vars.X), t(vars.X))), eq(
        eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.x),
        t(vars.y))), eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair,
        t(vars.y), t(vars.x)))))))))));

    step extend_predicate2(binary_commutative,
        and(eval_p2(binary, t(vars.f), t(vars.X)),
        any(vars.x, any(vars.y, implies(eval_p2(in,
        eval_f2(ordered_pair, t(vars.x), t(vars.y)),
        eval_f2(cartesian_product, t(vars.X), t(vars.X))), eq(
        eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair, t(vars.x),
        t(vars.y))), eval_f2(eval_map, t(vars.f), eval_f2(ordered_pair,
        t(vars.y), t(vars.x)))))))), vars.f, vars.X);
  }

  const binary_associative : Predicate2 {
    latex "\\mathrm{assoc} \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem binary_operation_associative() {
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

  const binary_has_left_identity : Predicate2 {
    latex "1_{\\mathrm{L}} \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem binary_operation_has_left_identity() {
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

  const binary_has_right_identity : Predicate2 {
    latex "1_{\\mathrm{R}} \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem binary_operation_has_right_identity() {
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

  const binary_has_identity : Predicate2 {
    latex "1 \\left( \\cdot_1 : \\cdot_2 \\times \\cdot_2 \\to \\cdot_2 \\right)";
  }

  theorem binary_operation_has_identity() {
    infer any(vars.f, any(vars.X, iff(eval_p2(binary_has_identity,
        t(vars.f), t(vars.X)), and(eval_p2(binary_has_left_identity,
        t(vars.f), t(vars.X)), eval_p2(binary_has_right_identity,
        t(vars.f), t(vars.X))))));

    step extend_predicate2(binary_has_identity,
        and(eval_p2(binary_has_left_identity,
        t(vars.f), t(vars.X)), eval_p2(binary_has_right_identity,
        t(vars.f), t(vars.X))), vars.f, vars.X);
  }

  const is_group : Predicate2 {
    latex "\\mathrm{grp} \\left( \\cdot_1 , \\cdot_2 \\right)";
  }
}
