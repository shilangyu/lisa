import java.time.Instant
object Test extends lisa.Main {
  import lisa.maths.settheory.*
  import lisa.maths.settheory.SetTheory.*
  import lisa.automation.settheory.SetTheoryTactics.*
  import lisa.maths.settheory.Comprehensions.*
  import lisa.maths.Quantifiers.*

  val x = variable
  val y = variable
  val z = variable
  val t = variable
  val p = variable
  val a = variable
  val b = variable
  val A = variable
  val B = variable
  val f = variable
  val g = variable
  val r = variable
  val fg = function[1]
  private val schemPred = predicate[1]
  private val P = predicate[1]
  private val h = formulaVariable

  /**
   * Sigma Pi
   */

  /**
   * Dependent Sum (Sigma)
   *
   * TODO: explain
   */

  val sigmaUniqueness = Theorem(
    ∃!(z, ∀(t, in(t, z) <=> ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a))))))
  ) {
    val defCondition = ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a))))
    val targetDef = ∀(t, in(t, z) <=> defCondition)
    val largerSet = cartesianProduct(A, union(relationRange(B)))
    val separationDef = ∀(t, in(t, z) <=> in(t, largerSet) /\ (defCondition))

    val inclusion = have(∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a)))) ==> in(t, cartesianProduct(A, union(relationRange(B))))) subproof {
      sorry
    }

    // TODO: extract to a tactic: using definition that do not fit UniqueComprehension because of a lacking larger set. Tactic should just accept a proof that existing conditions already imply belonging to some larger set
    have(thesis) by UniqueComprehension.fromOriginalSet(
      largerSet,
      lambda(t, defCondition),
      inclusion
    )

  }

  val Sigma = DEF(A, B) --> The(
    z,
    ∀(
      t,
      in(t, z)
        <=>
          (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a)))))
    )
  )(sigmaUniqueness)

  // TODO: definitions:
  // Union over a mapped set U_{a \in A} f(a) = U{f(a) | a \in A}
  // ---
  // TODO: theorems:
  // Sigma generalizes cartesian product (when 'a' is not used) -- Sigma(A,B) = A x B
  // Sigma is a subset of the cartesian product -- Sigma(A,B) ⊆ A x B
  // Pi with empty set is empty -- Pi({}, B) = P({})
  // Pi generalizes function space (when 'a' is not used) -- Pi(A,B) = A -> B
  // Pi is a subset of the space of functions -- Pi(A,B) ⊆ A -> B

  val sigmaWithEmptySet = Theorem(
    () |- Sigma(∅, B) === ∅
  ) {
    have(∀(t, in(t, Sigma(∅, B)) <=> (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, ∅) /\ in(b, app(B, a))))))) by InstantiateForall(Sigma(∅, B))(
      Sigma.definition of (A -> ∅)
    )
    val sigmaDef = thenHave(in(t, Sigma(∅, B)) <=> (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, ∅) /\ in(b, app(B, a)))))) by InstantiateForall(t)

    val emptySetDef = have(in(t, ∅) <=> (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, ∅) /\ in(b, app(B, a)))))) subproof {
      val lhs = have(in(t, ∅) |- (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, ∅) /\ in(b, app(B, a)))))) by Weakening(
        emptySet.definition of (x -> t)
      )

      have(((t === pair(a, b)) /\ in(a, ∅) /\ in(b, app(B, a))) |- in(t, ∅)) by Weakening(emptySet.definition of (x -> a))
      thenHave(∃(b, (t === pair(a, b)) /\ in(a, ∅) /\ in(b, app(B, a))) |- in(t, ∅)) by LeftExists
      val rhs = thenHave(∃(a, ∃(b, ((t === pair(a, b)) /\ in(a, ∅) /\ in(b, app(B, a))))) |- in(t, ∅)) by LeftExists

      have(thesis) by Tautology.from(lhs, rhs)
    }

    have(in(t, Sigma(∅, B)) <=> in(t, ∅)) by Tautology.from(sigmaDef, emptySetDef)
    val ext = thenHave(∀(t, in(t, Sigma(∅, B)) <=> in(t, ∅))) by RightForall

    have(thesis) by Tautology.from(ext, extensionalityAxiom of (x -> Sigma(∅, B), y -> ∅))
  }

  val firstInSigma = Theorem(
    in(p, Sigma(A, B)) |- in(firstInPair(p), A)
  ) {
    sorry
  }

  val secondInSigma = Theorem(
    in(p, Sigma(A, B)) |- in(secondInPair(p), app(B, firstInPair(p)))
  ) {
    sorry
  }

  val sigmaIsCartesianProductWhenBIsConstant = Theorem(
    ∀(a, in(a, A) ==> (app(f, a) === B)) |- Sigma(A, f) === cartesianProduct(A, B)
  ) {
    sorry
  }

  val piUniqueness = Theorem(
    ∃!(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))))
  ) {
    have(thesis) by UniqueComprehension(
      powerSet(Sigma(x, f)),
      lambda(z, (subset(x, relationDomain(z)) /\ functional(z)))
    )
  }

  /**
   * Dependent Product (Pi)
   *
   * TODO: explain
   */
  val Pi = DEF(x, f) --> The(
    z,
    ∀(
      g,
      in(g, z)
        <=>
          (in(g, powerSet(Sigma(x, f))) /\ (subset(x, relationDomain(g)) /\ functional(g)))
    )
  )(piUniqueness)

  val powerSetEmptySet = Theorem(
    () |- powerSet(∅) === singleton(∅)
  ) {
    val powerAx = have(in(x, powerSet(∅)) <=> subset(x, ∅)) by Weakening(powerAxiom of (y := ∅))

    have(in(x, powerSet(∅)) <=> in(x, singleton(∅))) by Tautology.from(
      powerAx,
      emptySetIsItsOwnOnlySubset,
      singletonHasNoExtraElements of (y := x, x := ∅)
    )
    val ext = thenHave(∀(x, in(x, powerSet(∅)) <=> in(x, singleton(∅)))) by RightForall

    have(thesis) by Tautology.from(ext, extensionalityAxiom of (x := powerSet(∅), y := singleton(∅)))
  }

  val emptySetFunctional = Theorem(
    functional(∅)
  ) {
    val isRelation = have(relation(∅)) subproof {
      // ∅ ⊆ A x B, so it must be a (empty) relation
      have(relationBetween(∅, a, b)) by Tautology.from(emptySetIsASubset of (x := cartesianProduct(a, b)), relationBetween.definition of (r := ∅))
      thenHave(∃(b, relationBetween(∅, a, b))) by RightExists
      val relationSpec = thenHave(∃(a, ∃(b, relationBetween(∅, a, b)))) by RightExists

      have(thesis) by Tautology.from(relationSpec, relation.definition of (r := ∅))
    }

    val uniqueY = have(∀(x, ∃(y, in(pair(x, y), ∅)) ==> ∃!(y, in(pair(x, y), ∅)))) subproof {
      // contradiction directly from the emptySetAxiom: there is nothing in the empty set
      have(in(pair(x, y), ∅) |- ∃!(y, in(pair(x, y), ∅))) by Tautology.from(emptySetAxiom of (x := pair(x, y)))
      thenHave(∃(y, in(pair(x, y), ∅)) |- ∃!(y, in(pair(x, y), ∅))) by LeftExists
      thenHave(∃(y, in(pair(x, y), ∅)) ==> ∃!(y, in(pair(x, y), ∅))) by Restate
      thenHave(thesis) by RightForall
    }

    have(thesis) by Tautology.from(isRelation, uniqueY, functional.definition of (f := ∅))
  }

  val piWithEmptySet = Theorem(
    () |- Pi(∅, f) === powerSet(∅)
  ) {
    have(∀(g, in(g, Pi(∅, f)) <=> (in(g, powerSet(Sigma(∅, f))) /\ (subset(∅, relationDomain(g)) /\ functional(g))))) by InstantiateForall(Pi(∅, f))(
      Pi.definition of (x -> ∅)
    )
    thenHave(∀(g, in(g, Pi(∅, f)) <=> (in(g, powerSet(∅)) /\ (subset(∅, relationDomain(g)) /\ functional(g))))) by Substitution.ApplyRules(sigmaWithEmptySet)
    val piDef = thenHave(in(g, Pi(∅, f)) <=> (in(g, powerSet(∅)) /\ (subset(∅, relationDomain(g)) /\ functional(g)))) by InstantiateForall(g)

    val lhs = have(in(g, Pi(∅, f)) ==> (in(g, powerSet(∅)))) by Weakening(piDef)

    val rhs = have(in(g, powerSet(∅)) ==> in(g, Pi(∅, f))) subproof {
      val assumption = assume(in(g, powerSet(∅)))

      have(in(g, singleton(∅))) by Substitution.ApplyRules(powerSetEmptySet)(assumption)
      val gIsEmpty = thenHave(g === ∅) by Substitution.ApplyRules(singletonHasNoExtraElements of (y := g, x := ∅))

      val isSubset = have(subset(∅, relationDomain(g))) by Weakening(emptySetIsASubset of (x := relationDomain(g)))

      have(functional(∅)) by Weakening(emptySetFunctional)
      val isFunctional = thenHave(functional(g)) by Substitution.ApplyRules(gIsEmpty)

      val result = have(in(g, Pi(∅, f))) by Tautology.from(piDef, assumption, isSubset, isFunctional)

      have(thesis) by Tautology.from(assumption, result)
    }

    have(in(g, Pi(∅, f)) <=> in(g, powerSet(∅))) by Tautology.from(lhs, rhs)
    val ext = thenHave(∀(g, in(g, Pi(∅, f)) <=> in(g, powerSet(∅)))) by RightForall

    have(thesis) by Tautology.from(ext, extensionalityAxiom of (x -> Pi(∅, f), y -> powerSet(∅)))
  }

  val piIsSetOfFunctionsWhenBIsConstant = Theorem(
    ∀(a, in(a, A) ==> (app(f, a) === B)) |- Pi(A, f) === setOfFunctions(A, B)
  ) {
    sorry
  }

  val inPiMeansSubsetOfSigma = Theorem(
    in(f, Pi(A, B)) |- subset(f, Sigma(A, B))
  ) {
    sorry
  }
}
