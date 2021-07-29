import "prop.sl";
import "pred.sl";
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
    require not_free(vars.x, $phi);

    infer implies(exists(vars.y, any(vars.x,
      iff(eval_p2(in, t(vars.x), t(vars.y)), $phi))),
      exists_unique(vars.y, any(vars.x,
      iff(eval_p2(in, t(vars.x), t(vars.y)), $phi))));
  }

  theorem
  equivalent_set_membership_condition(phi : Formula)
  {
    infer any(vars.x, any(vars.y, implies(and(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)), $phi)),
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.y)), $phi))),
      eq(t(vars.x), t(vars.y)))));

    step extensionality();
    step instantiation_elimination_meta(vars.x,
      any(vars.y, implies(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y)))), eq(t(vars.x), t(vars.y)))));
    step instantiation_elimination_meta(vars.y,
      implies(any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y)))), eq(t(vars.x), t(vars.y))));
    step conjunction_biconditional_elimination($phi,
      eval_p2(in, t(vars.z), t(vars.x)), eval_p2(in, t(vars.z), t(vars.y)));
    step quantified_conjunction_implication_meta(vars.z,
      iff(eval_p2(in, t(vars.z), t(vars.x)), $phi),
      iff(eval_p2(in, t(vars.z), t(vars.y)), $phi),
      iff(eval_p2(in, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y))));
    step hypothetical_syllogism_meta(and(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)), $phi)),
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.y)), $phi))),
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)),
      eval_p2(in, t(vars.z), t(vars.y)))), eq(t(vars.x), t(vars.y)));
    step generalization(vars.y, implies(and(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)), $phi)),
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.y)), $phi))),
      eq(t(vars.x), t(vars.y))));
    step generalization(vars.x, any(vars.y, implies(and(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)), $phi)),
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.y)), $phi))),
      eq(t(vars.x), t(vars.y)))));
  }

/*
  theorem
  set_membership_condition_unique(phi : Formula)
  {
    assume exists(vars.x, any(vars.z,
      iff(eval_p2(in, t(vars.z), t(vars.x)), $phi)));

    infer exists_unique(vars.x, any(vars.z,
      iff(eval_p2(in, t(vars.z), t(vars.x)), $phi)));

    step equivalent_set_membership_condition($phi);
    step conjunction_introduction_meta(exists(vars.x, any(vars.z,
      iff(eval_p2(in, t(vars.z), t(vars.x)), $phi))),
      any(vars.x, any(vars.y, implies(and(
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.x)), $phi)),
      any(vars.z, iff(eval_p2(in, t(vars.z), t(vars.y)), $phi))),
      eq(t(vars.x), t(vars.y))))));
    step existential_uniqueness(vars.x, , vars.y, )
  }
*/

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
    require cover_free(vars.x, $phi);

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

      /* step empty_set_exists(); */
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
