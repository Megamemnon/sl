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
  type Proposition;

  expr Proposition
  implies(phi : Proposition, psi : Proposition);

  expr Proposition
  not(phi : Proposition);

  axiom
  modus_ponens(phi : Proposition, psi : Proposition)
  {
    assume $phi;
    assume implies($phi, $psi);

    infer $psi;
  }

  axiom simplification(phi : Proposition, psi : Proposition)
  {
    infer implies($phi, implies($psi, $phi));
  }

  axiom distributive(phi : Proposition, psi : Proposition, chi : Proposition)
  {
    def A implies($phi, implies($psi, $chi));
    def B implies(implies($phi, $psi), implies($phi, $chi));

    infer implies(%A, %B);
  }

  axiom transposition(phi : Proposition, psi : Proposition)
  {
    infer implies(implies(not($psi), not($phi)), implies($phi, $psi));
  }

  theorem
  identity(phi : Proposition)
  {
    infer implies($phi, $phi);

    step simplification($phi, implies($phi, $phi));
    step distributive($phi, implies($phi, $phi), $phi);
    step modus_ponens(implies($phi, implies(implies($phi, $phi), $phi)),
      implies(implies($phi, implies($phi, $phi)), implies($phi, $phi)));
    step simplification($phi, $phi);
    step modus_ponens(implies($phi, implies($phi, $phi)), implies($phi, $phi));
  }
}
