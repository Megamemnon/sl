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
      x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    infer implies(exists($x, any($z, iff(eval_p2(in, t($z),
        t($x)), $phi))), exists_unique($x, any($z,
        iff(eval_p2(in, t($z), t($x)), $phi))));

    def ex exists($x, any($z, iff(eval_p2(in, t($z), t($x)),
        $phi)));
    def uniq any($x, any($y, implies(and(
        any($z, iff(eval_p2(in, t($z), t($x)), $phi)),
        any($z, iff(eval_p2(in, t($z), t($y)), $phi))),
        eq(t($x), t($y)))));

    step conjunction_introduction(%uniq, %ex);
    step conjunction_commutation(%uniq, %ex);
    step equivalent_set_membership_condition($phi, $x, $y, $z);
    step modus_ponens(%uniq, implies(%ex, and(%uniq, %ex)));
    step hypothetical_syllogism_meta(%ex, and(%uniq, %ex), and(%ex, %uniq));
    step existential_uniqueness($x, any($z, iff(
        eval_p2(in, t($z), t($x)), $phi)), $y,
        any($z, iff(eval_p2(in, t($z), t($y)), $phi)));
    step biconditional_elimination_left_meta(exists_unique($x,
        any($z, iff(eval_p2(in, t($z), t($x)), $phi))),
        and(exists($x, any($z,
        iff(eval_p2(in, t($z), t($x)), $phi))),
        any($x, any($y, implies(and(any($z,
        iff(eval_p2(in, t($z), t($x)), $phi)),
        any($z, iff(eval_p2(in, t($z), t($y)), $phi))),
        eq(t($x), t($y)))))));
    step hypothetical_syllogism_meta(%ex, and(%ex, %uniq),
        exists_unique($x, any($z, iff(eval_p2(in, t($z),
        t($x)), $phi))));
  }

  theorem set_membership_condition_unique_meta(phi : Formula,
      x : Variable, y : Variable, z : Variable) {
    require distinct($x, $y, $z);

    assume exists($x, any($z, iff(eval_p2(in, t($z), t($x)), $phi)));

    infer exists_unique($x, any($z, iff(eval_p2(in, t($z), t($x)), $phi)));

    step set_membership_condition_unique($phi, $x, $y, $z);
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
    require cover_free($x, $phi);

    infer any($z, exists($y, any($x,
        iff(eval_p2(in, t($x), t($y)),
        and(eval_p2(in, t($x), t($z)), $phi)))));
  }

  /* TODO: prove this from specification. */
  axiom set_extraction(phi : Formula, x : Variable, y : Variable) {
    require distinct($x, $y);
    require cover_free($y, $phi);

    infer implies(exists($x, any($y, implies($phi,
        eval_p2(in, t($y), t($x))))),
        exists($x, any($y, iff(eval_p2(in, t($y), t($x)), $phi))));
  }

  theorem set_extraction_unique_meta(phi : Formula, x : Variable,
      y : Variable) {
    require distinct($x, $y);
    require cover_free($y, $phi);

    assume exists($x, any($y, implies($phi, eval_p2(in, t($y), t($x)))));

    infer exists_unique($x, any($y, iff(eval_p2(in, t($y), t($x)), $phi)));

    step set_extraction($phi, $x, $y);
    step modus_ponens(exists($x, any($y, implies($phi,
        eval_p2(in, t($y), t($x))))),
        exists($x, any($y, iff(eval_p2(in, t($y), t($x)), $phi))));
    step set_membership_condition_unique_meta($phi, $x, vars.dummyz, $y);
  }

  const empty : Function0 {
    latex "\\emptyset";
  }

  namespace lemma {
    /* TODO: Since $z is not referenced outside of the proof, a dummy variable,
       guaranteed to be distinct from all other variables referenced in the
       proof, should be provided by the program (after applying an appropriate
       qualifier to the Variable type). */
    theorem empty_set_exists(x : Variable, y : Variable, z : Variable) {
      require distinct($x, $y, $z);

      dummy _z : Variable;

      infer exists($y, any($x, not(eval_p2(in, t($x),
          t($y)))));

      step specification(F, $x, $y, $z);
      step false();
      step negative_conjunction_introduction(F,
          eval_p2(in, t($x), t($z)));
      step modus_ponens(not(F), not(and(eval_p2(in, t($x), t($z)),
          F)));
      step instantiation_elimination($z, exists($y, any($x,
          iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t($z)), F)))));
      step modus_ponens(any($z, exists($y, any($x,
          iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t($z)), F))))),
          exists($y, any($x,
          iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t($z)), F)))));
      step identity(iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t($z)), F)));
      step infer_negated_equivalent(iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t($z)), F)),
          eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t($z)), F));
      step implication_generalization($x, iff(eval_p2(in, t($x),
          t($y)), and(eval_p2(in, t($x), t($z)), F)),
          not(eval_p2(in, t($x), t($y))));
      step implication_generalization_existential($y,
          any($x, iff(eval_p2(in, t($x),
          t($y)), and(eval_p2(in, t($x), t($z)), F))),
          any($x, not(eval_p2(in, t($x), t($y)))));
      step modus_ponens(exists($y, any($x,
          iff(eval_p2(in, t($x), t($y)), and(
          eval_p2(in, t($x), t($z)), F)))),
          exists($y, any($x, not(eval_p2(in, t($x), t($y))))));
    }

    /* TODO: this can be inferred from set_builder_uniqueness. */
    theorem empty_set_unique(x : Variable, y : Variable, z : Variable) {
      require distinct($x, $y, $z);

      infer exists_unique($y, any($x, not(eval_p2(in, t($x), t($y)))));

      step empty_set_exists($x, $y, $z);
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
      step set_membership_condition_unique(F, $y, $z, $x);
      step modus_ponens(exists($y, any($x, iff(eval_p2(in, t($x), t($y)), F))),
          exists_unique($y, any($x, iff(eval_p2(in, t($x), t($y)), F))));
      step existential_uniqueness_biconditional($y, $z,
          any($x, not(eval_p2(in, t($x), t($y)))),
          any($x, iff(eval_p2(in, t($x), t($y)), F)),
          any($x, not(eval_p2(in, t($x), t($z)))),
          any($x, iff(eval_p2(in, t($x), t($z)), F)));
      step biconditional_elimination_left_meta(
          exists_unique($y, any($x, not(eval_p2(in, t($x), t($y))))),
          exists_unique($y, any($x, iff(eval_p2(in, t($x), t($y)), F))));
      step modus_ponens(
          exists_unique($y, any($x, iff(eval_p2(in, t($x), t($y)), F))),
          exists_unique($y, any($x, not(eval_p2(in, t($x), t($y))))));
    }
  }

  theorem empty_set() {
    infer any(vars.x, not(eval_p2(in, t(vars.x), eval_f0(empty))));

    step lemma.empty_set_exists(vars.x, vars.y, vars.z);
    step lemma.empty_set_unique(vars.x, vars.y, vars.z);
    step extend_function0(empty,
        any(vars.x, not(eval_p2(in, t(vars.x), t(vars.y)))),
        any(vars.x, not(eval_p2(in, t(vars.x), eval_f0(empty)))));
  }

  axiom pairing(x : Variable, y : Variable, z : Variable) {
    infer any($x, any($y, exists($z, and(
        eval_p2(in, t($x), t($z)),
        eval_p2(in, t($y), t($z))))));
  }

  const singleton : Function1 {
    latex "\\{ \\cdot_1 \\}";
  }

  namespace lemma {
    /* TODO: prove this from pairing. */
    axiom singleton_exists() {
      infer any(vars.a, exists(vars.y, any(vars.x, iff(
          eval_p2(in, t(vars.x), t(vars.y)), eq(t(vars.x), t(vars.a))))));
    }

    axiom singleton_unique() {
      infer any(vars.a, exists_unique(vars.y, any(vars.x, iff(
          eval_p2(in, t(vars.x), t(vars.y)), eq(t(vars.x), t(vars.a))))));
    }
  }

  theorem singleton_containing() {
    infer any(vars.a, any(vars.x, iff(eval_p2(in, t(vars.x),
        eval_f1(singleton, t(vars.a))), eq(t(vars.x), t(vars.a)))));

    step lemma.singleton_unique();
    step extend_function1(singleton, any(vars.x, iff(
        eval_p2(in, t(vars.x), t(vars.y)), eq(t(vars.x), t(vars.a)))),
        any(vars.x, iff(eval_p2(in, t(vars.x), eval_f1(singleton, t(vars.a))),
        eq(t(vars.x), t(vars.a)))), vars.a);
  }

  const pair : Function2 {
    latex "\\{ \\cdot_1 , \\cdot_2 \\}";
  }

  namespace lemma {
    /* TODO: prove this from pairing. */
    axiom pair_exists() {
      infer any(vars.a, any(vars.b, exists(vars.y, any(vars.x,
          iff(eval_p2(in, t(vars.x), t(vars.y)),
          or(eq(t(vars.x), t(vars.a)), eq(t(vars.x), t(vars.b))))))));
    }

    axiom pair_unique() {
      infer any(vars.a, any(vars.b, exists_unique(vars.y, any(vars.x,
          iff(eval_p2(in, t(vars.x), t(vars.y)),
          or(eq(t(vars.x), t(vars.a)), eq(t(vars.x), t(vars.b))))))));
    }
  }

  theorem pair_containing() {
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

  axiom union(F : Variable, A : Variable, Y : Variable, x : Variable) {
    infer any($F, exists($A, any($Y, any($x,
        implies(and(eval_p2(in, t($x), t($Y)), eval_p2(in, t($Y), t($F))),
        eval_p2(in, t($x), t($A)))))));
  }

  const union_of : Function1 {
    latex "\\cup \\cdot_1";
  }

  /* TODO: prove from the axiom of union. */
  axiom union_of_elements() {
    infer any(vars.a, any(vars.x, iff(eval_p2(in, t(vars.x),
        eval_f1(union_of, t(vars.a))), exists(vars.z, and(
        eval_p2(in, t(vars.x), t(vars.z)),
        eval_p2(in, t(vars.z), t(vars.a)))))));
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

  axiom infinity(X : Variable, y : Variable) {
    infer exists($X, and(eval_p2(in, eval_f0(empty), t($X)),
        any($y, implies(eval_p2(in, t($y), t($X)),
        eval_p2(in, eval_f1(successor, t($y)), t($X))))));
  }

  const subset : Predicate2 {
    latex "\\subset";
  }

  theorem subset_of() {
    infer any(vars.x, any(vars.y,
        iff(eval_p2(subset, t(vars.x), t(vars.y)),
        any(vars.z, implies(eval_p2(in, t(vars.z), t(vars.x)),
        eval_p2(in, t(vars.z), t(vars.y)))))));

    step extend_predicate2(subset, any(vars.z, implies(eval_p2(in, t(vars.z),
        t(vars.x)), eval_p2(in, t(vars.z), t(vars.y)))), vars.x, vars.y);
  }

  axiom power_set(x : Variable, y : Variable, z : Variable) {
    infer any($x, exists($y, any($z,
        implies(eval_p2(subset, t($z), t($x)),
        eval_p2(in, t($z), t($y))))));
  }

  const naturals_ordinals : Function0 {
    latex "\\mathbb{N}";
  }

  const zero_ordinal : Function0 {
    latex "0";
  }

  const ordered_pair : Function2 {
    latex "\\cdot_1 , \\cdot_2";
  }

  const cartesian_product : Function2 {
    latex "\\cdot_1 \\times \\cdot_2";
  }

  axiom cartesian_product_of_sets() {
    infer any(vars.A, any(vars.B, any(vars.x, iff(
        eval_p2(in, t(vars.x), eval_f2(cartesian_product, t(vars.A),
        t(vars.B))), exists(vars.a, exists(vars.b,
        and(and(eval_p2(in, t(vars.a), t(vars.A)),
        eval_p2(in, t(vars.b), t(vars.B))), eq(t(vars.x),
        eval_f2(ordered_pair, t(vars.a), t(vars.b))))))))));
  }

  const map : Predicate3 {
    latex "\\cdot_1 : \\cdot_2 \\to \\cdot_3";
  }

  axiom map_of_sets() {
    infer any(vars.f, any(vars.X, any(vars.Y, iff(
        eval_p3(map, t(vars.f), t(vars.X), t(vars.Y)),
        any(vars.x, implies(eval_p2(in, t(vars.x), t(vars.X)),
        exists_unique(vars.y, and(eval_p2(in, t(vars.y), t(vars.Y)),
        eval_p2(in, eval_f2(ordered_pair, t(vars.x), t(vars.y)),
        t(vars.f))))))))));
  }

  const eval_map : Function2 {
    latex "\\cdot_1 \\left( \\cdot_2 \\right)";
  }

  /* TODO: Formula the axiom of choice. */
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
