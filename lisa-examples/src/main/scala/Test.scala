import java.time.Instant
object Test extends lisa.Main {
  import lisa.maths.settheory.*
  import lisa.maths.settheory.SetTheory.*
  import lisa.automation.settheory.SetTheoryTactics.*
  import lisa.maths.settheory.Comprehensions.*
  import lisa.maths.Quantifiers.*
  import lisa.automation.kernel.CommonTactics.*

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
  private val Q = predicate[1]
  private val h = formulaVariable

  val inAppIsFunctional = Theorem(
    in(y, app(f, x)) |- functional(f) /\ in(x, relationDomain(f)) /\ in(pair(x, app(f, x)), f)
  ) {
    assume(in(y, app(f, x)))

    val appIsNotEmpty = have(!(app(f, x) === ∅)) by Tautology.from(
      setWithElementNonEmpty of (x := app(f, x))
    )

    val appDef = have(
      ((functional(f) /\ in(x, relationDomain(f))) ==> in(pair(x, app(f, x)), f))
        /\ ((!functional(f) \/ !in(x, relationDomain(f))) ==> (app(f, x) === ∅))
    ) by InstantiateForall(app(f, x))(
      app.definition
    )

    val isFunctional = have(functional(f) /\ in(x, relationDomain(f))) by Tautology.from(appDef, appIsNotEmpty)

    val pairIn = have(in(pair(x, app(f, x)), f)) by Tautology.from(
      appDef,
      isFunctional
    )

    have(thesis) by Tautology.from(isFunctional, pairIn)
  }

  val elemInItsPowerSet = Theorem(
    in(x, powerSet(x))
  ) {
    have(thesis) by Tautology.from(powerAxiom of (y := x), subsetReflexivity)
  }

  val constantFunction = DEF(x, t) --> cartesianProduct(x, singleton(t))

  val constantFunctionDomain = Theorem(
    relationDomain(constantFunction(x, t)) === x
  ) {
    val constFunDef = have((constantFunction(x, t) === cartesianProduct(x, singleton(t)))) by Weakening(constantFunction.definition of constantFunction(x, t))

    have(∀(p, in(p, relationDomain(constantFunction(x, t))) <=> ∃(a, in(pair(p, a), constantFunction(x, t))))) by InstantiateForall(relationDomain(constantFunction(x, t)))(
      relationDomain.definition of (r := constantFunction(x, t))
    )
    val domainDef = thenHave(in(p, relationDomain(constantFunction(x, t))) <=> ∃(a, in(pair(p, a), constantFunction(x, t)))) by InstantiateForall(p)

    val rhs = have(∃(a, in(pair(p, a), constantFunction(x, t))) ==> in(p, x)) subproof {
      val assumption = assume(∃(a, in(pair(p, a), constantFunction(x, t))))
      val aw = witness(assumption)
      have(in(pair(p, aw), constantFunction(x, t))) by Restate
      thenHave(in(pair(p, aw), cartesianProduct(x, singleton(t)))) by Substitution.ApplyRules(constFunDef)

      have(thesis) by Tautology.from(lastStep, pairInCartesianProduct of (a := p, b := aw, y := singleton(t)))
    }

    val lhs = have(in(p, x) ==> ∃(a, in(pair(p, a), constantFunction(x, t)))) subproof {
      assume(in(p, x))
      val tIn = have(in(t, singleton(t))) by Tautology.from(singletonHasNoExtraElements of (y := t, x := t))

      have(in(pair(p, t), cartesianProduct(x, singleton(t)))) by Tautology.from(
        pairInCartesianProduct of (a := p, b := t, y := singleton(t)),
        tIn
      )
      thenHave(∃(a, in(pair(p, a), cartesianProduct(x, singleton(t))))) by RightExists
      thenHave(∃(a, in(pair(p, a), constantFunction(x, t)))) by Substitution.ApplyRules(constFunDef)
    }

    have(in(p, x) <=> in(p, relationDomain(constantFunction(x, t)))) by Tautology.from(domainDef, rhs, lhs)
    val ext = thenHave(∀(p, in(p, x) <=> in(p, relationDomain(constantFunction(x, t))))) by RightForall

    have(thesis) by Tautology.from(ext, extensionalityAxiom of (y := relationDomain(constantFunction(x, t))))
  }

  val cartesianProductIsRelation = Theorem(
    relation(cartesianProduct(x, y))
  ) {
    have(relationBetween(cartesianProduct(x, y), x, y)) by Tautology.from(
      subsetReflexivity of (x := cartesianProduct(x, y)),
      relationBetween.definition of (r := cartesianProduct(x, y), a := x, b := y)
    )
    thenHave(∃(b, relationBetween(cartesianProduct(x, y), x, b))) by RightExists
    val relationSpec = thenHave(∃(a, ∃(b, relationBetween(cartesianProduct(x, y), a, b)))) by RightExists

    have(thesis) by Tautology.from(relationSpec, relation.definition of (r := cartesianProduct(x, y)))
  }

  val constantFunctionIsFunctional = Theorem(
    functional(constantFunction(x, t))
  ) {
    val constFunDef = have((constantFunction(x, t) === cartesianProduct(x, singleton(t)))) by Weakening(constantFunction.definition of constantFunction(x, t))

    val isRelation = have(relation(constantFunction(x, t))) subproof {
      have(relation(cartesianProduct(x, singleton(t)))) by Weakening(cartesianProductIsRelation of (y := singleton(t)))
      thenHave(thesis) by Substitution.ApplyRules(constFunDef)
    }

    val uniqueY = have(∀(a, ∃(y, in(pair(a, y), constantFunction(x, t))) ==> ∃!(y, in(pair(a, y), constantFunction(x, t))))) subproof {
      have(∃(y, in(pair(a, y), constantFunction(x, t))) ==> ∃!(y, in(pair(a, y), constantFunction(x, t)))) subproof {
        val existence = assume(∃(y, in(pair(a, y), constantFunction(x, t))))

        val uniqueness = have((in(pair(a, y), constantFunction(x, t)), in(pair(a, p), constantFunction(x, t))) |- (y === p)) subproof {
          val assumption1 = assume(in(pair(a, y), constantFunction(x, t)))
          val assumption2 = assume(in(pair(a, p), constantFunction(x, t)))

          have(in(pair(a, y), cartesianProduct(x, singleton(t)))) by Substitution.ApplyRules(constFunDef)(assumption1)
          val eq1 = have(y === t) by Tautology.from(
            pairInCartesianProduct of (b := y, y := singleton(t)),
            lastStep,
            singletonHasNoExtraElements of (x := t)
          )

          have(in(pair(a, p), cartesianProduct(x, singleton(t)))) by Substitution.ApplyRules(constFunDef)(assumption2)
          val eq2 = have(p === t) by Tautology.from(
            pairInCartesianProduct of (b := p, y := singleton(t)),
            lastStep,
            singletonHasNoExtraElements of (x := t, y := p)
          )

          have(y === p) by Tautology.from(eq1, eq2, equalityTransitivity of (x := y, y := t, z := p))
        }

        have(∃!(y, in(pair(a, y), constantFunction(x, t)))) by ExistenceAndUniqueness(in(pair(a, y), constantFunction(x, t)))(existence, uniqueness)
      }
      thenHave(thesis) by RightForall
    }

    have(thesis) by Tautology.from(isRelation, uniqueY, functional.definition of (f := constantFunction(x, t)))
  }

  val constantFunctionFunctionFrom = Theorem(
    functionFrom(constantFunction(x, t), x, singleton(t))
  ) {
    val constFunDef = have((constantFunction(x, t) === cartesianProduct(x, singleton(t)))) by Weakening(constantFunction.definition of constantFunction(x, t))

    have(∀(a, in(a, setOfFunctions(x, singleton(t))) <=> (in(a, powerSet(cartesianProduct(x, singleton(t)))) /\ functionalOver(a, x)))) by InstantiateForall(setOfFunctions(x, singleton(t)))(
      setOfFunctions.definition of (y := singleton(t))
    )
    val setOfFunctionsDef = thenHave(
      in(constantFunction(x, t), setOfFunctions(x, singleton(t))) <=> (in(constantFunction(x, t), powerSet(cartesianProduct(x, singleton(t)))) /\ functionalOver(constantFunction(x, t), x))
    ) by InstantiateForall(constantFunction(x, t))

    have(in(cartesianProduct(x, singleton(t)), powerSet(cartesianProduct(x, singleton(t))))) by Weakening(elemInItsPowerSet of (x := cartesianProduct(x, singleton(t))))
    val inPowerSet = thenHave(in(constantFunction(x, t), powerSet(cartesianProduct(x, singleton(t))))) by Substitution.ApplyRules(constFunDef)

    val funcOver = have(functionalOver(constantFunction(x, t), x)) by Tautology.from(
      constantFunctionIsFunctional,
      constantFunctionDomain,
      functionalOver.definition of (f := constantFunction(x, t))
    )

    have(thesis) by Tautology.from(
      inPowerSet,
      funcOver,
      setOfFunctionsDef,
      functionFrom.definition of (f := constantFunction(x, t), y := singleton(t))
    )
  }

  val functionFromApplication = Theorem(
    functionFrom(f, x, y) /\ in(a, x) |- in(app(f, a), y)
  ) {
    val funcFrom = assume(functionFrom(f, x, y))
    val inDomain = assume(in(a, x))

    val isFunctional = have(functional(f)) by Tautology.from(funcFrom, functionFromImpliesFunctional)
    val relDomainEq = have(relationDomain(f) === x) by Tautology.from(funcFrom, functionFromImpliesDomainEq)
    val inRelDomain = have(in(a, relationDomain(f))) by Substitution.ApplyRules(relDomainEq)(inDomain)

    val appDef = have(
      ((functional(f) /\ in(a, relationDomain(f))) ==> in(pair(a, app(f, a)), f))
        /\ ((!functional(f) \/ !in(a, relationDomain(f))) ==> (app(f, a) === ∅))
    ) by InstantiateForall(app(f, a))(
      app.definition of (x := a)
    )

    have(in(pair(a, app(f, a)), f)) by Tautology.from(
      isFunctional,
      inRelDomain,
      appDef
    )
    val pairInF = thenHave(∃(z, in(pair(z, app(f, a)), f))) by RightExists

    have(∀(t, in(t, relationRange(f)) <=> ∃(z, in(pair(z, t), f)))) by InstantiateForall(relationRange(f))(
      relationRange.definition of (r := f)
    )
    val rangeDef = thenHave(in(app(f, a), relationRange(f)) <=> ∃(z, in(pair(z, app(f, a)), f))) by InstantiateForall(app(f, a))

    val appInRange = have(in(app(f, a), relationRange(f))) by Tautology.from(rangeDef, pairInF)

    have(subset(relationRange(f), y)) by Weakening(functionImpliesRangeSubsetOfCodomain)
    thenHave(∀(z, in(z, relationRange(f)) ==> in(z, y))) by Substitution.ApplyRules(subsetAxiom of (x := relationRange(f)))
    thenHave(in(app(f, a), relationRange(f)) ==> in(app(f, a), y)) by InstantiateForall(app(f, a))

    have(thesis) by Tautology.from(appInRange, lastStep)
  }

  val constantFunctionApplication = Theorem(
    in(a, x) |- app(constantFunction(x, t), a) === t
  ) {
    assume(in(a, x))
    have(functionFrom(constantFunction(x, t), x, singleton(t))) by Weakening(constantFunctionFunctionFrom)

    have(in(app(constantFunction(x, t), a), singleton(t))) by Tautology.from(
      functionFromApplication of (f := constantFunction(x, t), y := singleton(t)),
      lastStep
    )

    have(thesis) by Tautology.from(
      singletonHasNoExtraElements of (y := app(constantFunction(x, t), a), x := t),
      lastStep
    )
  }

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
    val inclusion = have(∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a)))) ==> in(t, cartesianProduct(A, union(relationRange(B))))) subproof {
      assume(∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a)))))
      val aw = witness(lastStep)
      have(∃(b, (t === pair(aw, b)) /\ in(aw, A) /\ in(b, app(B, aw)))) by Restate
      val bw = witness(lastStep)
      val isPair = have(t === pair(aw, bw)) by Restate
      val inA = have(in(aw, A)) by Restate
      val inBApp = have(in(bw, app(B, aw))) by Restate

      val inUnion = have(in(bw, union(relationRange(B)))) subproof {
        val inRange = have(in(app(B, aw), relationRange(B))) subproof {
          have(in(pair(aw, app(B, aw)), B)) by Tautology.from(inAppIsFunctional of (f := B, x := aw, y := bw), inBApp)
          val rangeCondition = thenHave(∃(a, in(pair(a, app(B, aw)), B))) by RightExists

          have(∀(t, in(t, relationRange(B)) <=> ∃(a, in(pair(a, t), B)))) by InstantiateForall(relationRange(B))(
            relationRange.definition of (r -> B)
          )
          val rangeDef = thenHave(in(app(B, aw), relationRange(B)) <=> ∃(a, in(pair(a, app(B, aw)), B))) by InstantiateForall(app(B, aw))

          have(thesis) by Tautology.from(rangeDef, rangeCondition)
        }

        // using the definition of a union with app(B, aw) as the intermediate set
        have(in(app(B, aw), relationRange(B)) /\ in(bw, app(B, aw))) by Tautology.from(inRange, inBApp)
        thenHave(∃(y, in(y, relationRange(B)) /\ in(bw, y))) by RightExists.withParameters(in(y, relationRange(B)) /\ in(bw, y), y, app(B, aw))
        thenHave(thesis) by Substitution.ApplyRules(unionAxiom of (x := relationRange(B), z := bw))
      }

      have(in(aw, A) /\ in(bw, union(relationRange(B)))) by Tautology.from(inA, inUnion)
      have(in(pair(aw, bw), cartesianProduct(A, union(relationRange(B))))) by Tautology.from(
        lastStep,
        pairInCartesianProduct of (a := aw, b := bw, x := A, y := union(relationRange(B)))
      )
      thenHave(in(t, cartesianProduct(A, union(relationRange(B))))) by Substitution.ApplyRules(isPair)
    }

    have(thesis) by UniqueComprehension.fromOriginalSet(
      cartesianProduct(A, union(relationRange(B))),
      lambda(t, ∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a))))),
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
  // Sigma is a subset of the cartesian product -- Sigma(A,B) ⊆ A x B[A]
  // Sigma is exactly cartesian product iff 'a' is not used -- B const <-> Sigma(A,B) = A x B[A]
  // Pi is a subset of the space of functions -- Pi(A,B) ⊆ A -> B[A]
  // Pi is exactly function space iff 'a' is not used -- B const <-> Pi(A,B) = A -> B[A]

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
    assume(in(p, Sigma(A, B)))

    have(∀(t, in(t, Sigma(A, B)) <=> (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a))))))) by InstantiateForall(Sigma(A, B))(
      Sigma.definition
    )
    thenHave(in(p, Sigma(A, B)) <=> (∃(a, ∃(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a)))))) by InstantiateForall(p)
    thenHave(∃(a, ∃(b, (p === pair(a, b)) /\ in(a, A)))) by Tautology

    val aw = witness(lastStep)
    thenHave(∃(b, (p === pair(aw, b)) /\ in(aw, A))) by Restate
    val bw = witness(lastStep)
    val isPairAndInA = thenHave((p === pair(aw, bw)) /\ in(aw, A)) by Restate
    val isPair = have(p === pair(aw, bw)) by Weakening(isPairAndInA)
    val inA = have(in(aw, A)) by Weakening(isPairAndInA)

    val first = have(firstInPair(pair(aw, bw)) === aw) by Tautology.from(firstInPairReduction of (x := aw, y := bw))

    have(in(firstInPair(pair(aw, bw)), A)) by Substitution.ApplyRules(first)(inA)
    thenHave(thesis) by Substitution.ApplyRules(isPair)
  }

  val secondInSigma = Theorem(
    in(p, Sigma(A, B)) |- in(secondInPair(p), app(B, firstInPair(p)))
  ) {
    assume(in(p, Sigma(A, B)))

    have(∀(t, in(t, Sigma(A, B)) <=> (∃(a, ∃(b, (t === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a))))))) by InstantiateForall(Sigma(A, B))(
      Sigma.definition
    )
    thenHave(in(p, Sigma(A, B)) <=> (∃(a, ∃(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a)))))) by InstantiateForall(p)
    thenHave(∃(a, ∃(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, app(B, a))))) by Tautology

    val aw = witness(lastStep)
    thenHave(∃(b, (p === pair(aw, b)) /\ in(aw, A) /\ in(b, app(B, aw)))) by Restate
    val bw = witness(lastStep)
    val isPairAndInAAndBInApp = thenHave((p === pair(aw, bw)) /\ in(aw, A) /\ in(bw, app(B, aw))) by Restate
    val isPair = have(p === pair(aw, bw)) by Weakening(isPairAndInAAndBInApp)
    val inA = have(in(aw, A)) by Weakening(isPairAndInAAndBInApp)
    val BInApp = have(in(bw, app(B, aw))) by Weakening(isPairAndInAAndBInApp)

    val first = have(firstInPair(pair(aw, bw)) === aw) by Tautology.from(firstInPairReduction of (x := aw, y := bw))
    val second = have(secondInPair(pair(aw, bw)) === bw) by Tautology.from(secondInPairReduction of (x := aw, y := bw))

    have(in(secondInPair(pair(aw, bw)), app(B, firstInPair(pair(aw, bw))))) by Substitution.ApplyRules(first, second)(BInApp)
    thenHave(thesis) by Substitution.ApplyRules(isPair)
  }

  val sigmaIsCartesianProductWhenBIsConstant = Theorem(
    Sigma(A, constantFunction(A, t)) === cartesianProduct(A, t)
  ) {
    have(∀(p, in(p, Sigma(A, constantFunction(A, t))) <=> (∃(a, ∃(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a))))))) by InstantiateForall(
      Sigma(A, constantFunction(A, t))
    )(
      Sigma.definition of (B -> constantFunction(A, t))
    )
    val sigmaDef = thenHave(in(p, Sigma(A, constantFunction(A, t))) <=> (∃(a, ∃(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a)))))) by InstantiateForall(p)

    have((in(a, A) /\ in(b, app(constantFunction(A, t), a))) <=> (in(a, A) /\ in(b, t))) subproof {
      val constApp = have(in(a, A) <=> (in(a, A) /\ (app(constantFunction(A, t), a) === t))) by Tautology.from(
        constantFunctionApplication of (x := A)
      )

      val lhs = have(in(a, A) /\ in(b, app(constantFunction(A, t), a)) |- (in(a, A) /\ in(b, t))) subproof {
        val inA = assume(in(a, A))
        val subst = have(app(constantFunction(A, t), a) === t) by Tautology.from(constApp, inA)

        assume(in(b, app(constantFunction(A, t), a)))
        thenHave(in(a, A) /\ in(b, app(constantFunction(A, t), a))) by Tautology
        thenHave(thesis) by Substitution.ApplyRules(subst)
      }

      val rhs = have(in(a, A) /\ in(b, t) |- (in(a, A) /\ in(b, app(constantFunction(A, t), a)))) subproof {
        val inA = assume(in(a, A))
        val subst = have(app(constantFunction(A, t), a) === t) by Tautology.from(constApp, inA)

        assume(in(b, t))
        thenHave(in(a, A) /\ in(b, t)) by Tautology
        thenHave(thesis) by Substitution.ApplyRules(subst)
      }

      have(thesis) by Tautology.from(lhs, rhs)
    }
    have(((p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a))) <=> ((p === pair(a, b)) /\ in(a, A) /\ in(b, t))) by Tautology.from(lastStep)
    thenHave(∀(b, ((p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a))) <=> ((p === pair(a, b)) /\ in(a, A) /\ in(b, t)))) by RightForall
    have(∃(b, ((p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a)))) <=> ∃(b, ((p === pair(a, b)) /\ in(a, A) /\ in(b, t)))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a))), Q := lambda(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, t)))
    )
    thenHave(∀(a, ∃(b, ((p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a)))) <=> ∃(b, ((p === pair(a, b)) /\ in(a, A) /\ in(b, t))))) by RightForall
    val constApp = have(∃(a, ∃(b, ((p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a))))) <=> ∃(a, ∃(b, ((p === pair(a, b)) /\ in(a, A) /\ in(b, t))))) by Cut(
      lastStep,
      existentialEquivalenceDistribution of (P := lambda(a, ∃(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, app(constantFunction(A, t), a)))), Q := lambda(
        a,
        ∃(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, t))
      ))
    )
    val simplSigmaDef = have(in(p, Sigma(A, constantFunction(A, t))) <=> (∃(a, ∃(b, (p === pair(a, b)) /\ in(a, A) /\ in(b, t))))) by Substitution.ApplyRules(constApp)(sigmaDef)

    have(in(p, Sigma(A, constantFunction(A, t))) <=> in(p, cartesianProduct(A, t))) by Tautology.from(simplSigmaDef, elemOfCartesianProduct of (x := A, y := t, t := p))
    val ext = thenHave(∀(p, in(p, Sigma(A, constantFunction(A, t))) <=> in(p, cartesianProduct(A, t)))) by RightForall

    have(thesis) by Tautology.from(ext, extensionalityAxiom of (x := Sigma(A, constantFunction(A, t)), y := cartesianProduct(A, t)))
  }

  val piUniqueness = Theorem(
    ∃!(z, ∀(g, in(g, z) <=> (in(g, powerSet(Sigma(x, f))) /\ functionalOver(g, x))))
  ) {
    have(thesis) by UniqueComprehension(
      powerSet(Sigma(x, f)),
      lambda(z, functionalOver(z, x))
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
          (in(g, powerSet(Sigma(x, f))) /\ functionalOver(g, x))
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

  val domainOfEmptySetIsEmpty = Theorem(
    ∅ === relationDomain(∅)
  ) {
    have(∀(t, in(t, relationDomain(∅)) <=> ∃(a, in(pair(t, a), ∅)))) by InstantiateForall(relationDomain(∅))(
      relationDomain.definition of (r := ∅)
    )
    val domainDef = thenHave(in(t, relationDomain(∅)) <=> ∃(a, in(pair(t, a), ∅))) by InstantiateForall(t)
    val contraPosDomainDef = have(!in(t, relationDomain(∅)) <=> ∀(a, !in(pair(t, a), ∅))) by Tautology.from(domainDef)
    have(!in(pair(t, a), ∅)) by Tautology.from(emptySetAxiom of (x := pair(t, a)))
    val nothingInEmpty = thenHave(∀(a, !in(pair(t, a), ∅))) by RightForall

    have(!in(t, relationDomain(∅))) by Tautology.from(nothingInEmpty, contraPosDomainDef)
    thenHave(∀(t, !in(t, relationDomain(∅)))) by RightForall

    have(thesis) by Tautology.from(lastStep, setWithNoElementsIsEmpty of (x := relationDomain(∅)))
  }

  val piWithEmptySet = Theorem(
    () |- Pi(∅, f) === powerSet(∅)
  ) {
    have(∀(g, in(g, Pi(∅, f)) <=> (in(g, powerSet(Sigma(∅, f))) /\ functionalOver(g, ∅)))) by InstantiateForall(Pi(∅, f))(
      Pi.definition of (x -> ∅)
    )
    thenHave(∀(g, in(g, Pi(∅, f)) <=> (in(g, powerSet(∅)) /\ functionalOver(g, ∅)))) by Substitution.ApplyRules(sigmaWithEmptySet)
    val piDef = thenHave(in(g, Pi(∅, f)) <=> (in(g, powerSet(∅)) /\ functionalOver(g, ∅))) by InstantiateForall(g)

    val lhs = have(in(g, Pi(∅, f)) ==> (in(g, powerSet(∅)))) by Weakening(piDef)

    val rhs = have(in(g, powerSet(∅)) ==> in(g, Pi(∅, f))) subproof {
      val assumption = assume(in(g, powerSet(∅)))

      have(in(g, singleton(∅))) by Substitution.ApplyRules(powerSetEmptySet)(assumption)
      val gIsEmpty = thenHave(g === ∅) by Substitution.ApplyRules(singletonHasNoExtraElements of (y := g, x := ∅))

      have(∅ === relationDomain(∅)) by Weakening(domainOfEmptySetIsEmpty)
      val isDomain = thenHave(∅ === relationDomain(g)) by Substitution.ApplyRules(gIsEmpty)

      have(functional(∅)) by Weakening(emptySetFunctional)
      val isFunctional = thenHave(functional(g)) by Substitution.ApplyRules(gIsEmpty)

      val isFunctionalOver = have(functionalOver(g, ∅)) by Tautology.from(
        functionalOver.definition of (f := g, x := ∅),
        isFunctional,
        isDomain
      )

      val result = have(in(g, Pi(∅, f))) by Tautology.from(piDef, assumption, isFunctionalOver)

      have(thesis) by Tautology.from(assumption, result)
    }

    have(in(g, Pi(∅, f)) <=> in(g, powerSet(∅))) by Tautology.from(lhs, rhs)
    val ext = thenHave(∀(g, in(g, Pi(∅, f)) <=> in(g, powerSet(∅)))) by RightForall

    have(thesis) by Tautology.from(ext, extensionalityAxiom of (x -> Pi(∅, f), y -> powerSet(∅)))
  }

  val piIsSetOfFunctionsWhenBIsConstant = Theorem(
    Pi(A, constantFunction(A, t)) === setOfFunctions(A, t)
  ) {
    have(∀(g, in(g, setOfFunctions(A, t)) <=> (in(g, powerSet(cartesianProduct(A, t))) /\ functionalOver(g, A)))) by InstantiateForall(setOfFunctions(A, t))(
      setOfFunctions.definition of (x -> A, y -> t)
    )
    val setOfFunctionsDef = thenHave(in(g, setOfFunctions(A, t)) <=> (in(g, powerSet(cartesianProduct(A, t))) /\ functionalOver(g, A))) by InstantiateForall(g)

    have(∀(g, in(g, Pi(A, constantFunction(A, t))) <=> (in(g, powerSet(Sigma(A, constantFunction(A, t)))) /\ functionalOver(g, A)))) by InstantiateForall(Pi(A, constantFunction(A, t)))(
      Pi.definition of (x -> A, f -> constantFunction(A, t))
    )
    thenHave(∀(g, in(g, Pi(A, constantFunction(A, t))) <=> (in(g, powerSet(cartesianProduct(A, t))) /\ functionalOver(g, A)))) by Substitution.ApplyRules(sigmaIsCartesianProductWhenBIsConstant)
    thenHave(in(g, Pi(A, constantFunction(A, t))) <=> (in(g, powerSet(cartesianProduct(A, t))) /\ functionalOver(g, A))) by InstantiateForall(g)
    thenHave(in(g, Pi(A, constantFunction(A, t))) <=> in(g, setOfFunctions(A, t))) by Substitution.ApplyRules(setOfFunctionsDef)
    val ext = thenHave(∀(g, in(g, Pi(A, constantFunction(A, t))) <=> in(g, setOfFunctions(A, t)))) by RightForall

    have(thesis) by Tautology.from(
      ext,
      extensionalityAxiom of (x := Pi(A, constantFunction(A, t)), y := setOfFunctions(A, t))
    )
  }
}
