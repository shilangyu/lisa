package lisa.proven.peano_example

import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.RunningTheory
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import lisa.proven.tactics.ProofTactics.*
import lisa.utils.Helpers.{_, given}
import lisa.utils.Library
import lisa.utils.Printer

object Peano {
  export PeanoArithmeticsLibrary.{*, given}

  /////////////////////////// OUTPUT CONTROL //////////////////////////
  given output: (String => Unit) = println
  given finishOutput: (Throwable => Nothing) = e => throw e

  def main(args: Array[String]): Unit = {}
  /////////////////////////////////////////////////////////////////////

  def instantiateForallImport(proofImport: Sequent, t: Peano.Term): SCProof = {
    require(proofImport.right.size == 1)
    val formula = proofImport.right.head
    require(formula.isInstanceOf[BinderFormula] && formula.asInstanceOf[BinderFormula].label == Forall)
    val forall = formula.asInstanceOf[BinderFormula]
    instantiateForall(SCProof(IndexedSeq(), IndexedSeq(proofImport)))
    val tempVar = VariableLabel(freshId(formula.freeVariables.map(_.id), "x"))
    val instantiated = instantiateBinder(forall, t)
    val p1 = Hypothesis(instantiated |- instantiated, instantiated)
    val p2 = LeftForall(formula |- instantiated, 0, instantiateBinder(forall, tempVar), tempVar, t)
    val p3 = Cut(() |- instantiated, -1, 1, formula)
    Proof(IndexedSeq(p1, p2, p3), IndexedSeq(proofImport))
  }

  def applyInduction(baseProof: SCSubproof, inductionStepProof: SCSubproof, inductionInstance: SCProofStep): IndexedSeq[SCProofStep] = {
    require(baseProof.bot.right.size == 1, s"baseProof should prove exactly one formula, got ${Printer.prettySequent(baseProof.bot)}")
    require(inductionStepProof.bot.right.size == 1, s"inductionStepProof should prove exactly one formula, got ${Printer.prettySequent(inductionStepProof.bot)}")
    require(
      inductionInstance.bot.left.isEmpty && inductionInstance.bot.right.size == 1,
      s"induction instance step should have nothing on the left and exactly one formula on the right, got ${Printer.prettySequent(inductionInstance.bot)}"
    )
    val (premise, conclusion) = (inductionInstance.bot.right.head match {
      case ConnectorFormula(Implies, Seq(premise, conclusion)) => (premise, conclusion)
      case _ => require(false, s"induction instance should be of the form A => B, got ${Printer.prettyFormula(inductionInstance.bot.right.head)}")
    })
    val baseFormula = baseProof.bot.right.head
    val stepFormula = inductionStepProof.bot.right.head
    require(
      isSame(baseFormula /\ stepFormula, premise),
      "induction instance premise should be of the form base /\\ step, got " +
        s"premise: ${Printer.prettyFormula(premise)}, base: ${Printer.prettyFormula(baseFormula)}, step: ${Printer.prettyFormula(stepFormula)}"
    )

    val lhs: Set[Formula] = baseProof.bot.left ++ inductionStepProof.bot.left
    val base0 = baseProof
    val step1 = inductionStepProof
    val instance2 = inductionInstance
    val inductionPremise3 = RightAnd(lhs |- baseFormula /\ stepFormula, Seq(0, 1), Seq(baseFormula, stepFormula))
    val hypConclusion4 = hypothesis(conclusion)
    val inductionInstanceOnTheLeft5 = LeftImplies(lhs + (premise ==> conclusion) |- conclusion, 3, 4, premise, conclusion)
    val cutInductionInstance6 = Cut(lhs |- conclusion, 2, 5, premise ==> conclusion)
    IndexedSeq(base0, step1, instance2, inductionPremise3, hypConclusion4, inductionInstanceOnTheLeft5, cutInductionInstance6)
  }

  val (y1, z1) =
    (VariableLabel("y1"), VariableLabel("z1"))

  THEOREM("x + 0 = 0 + x") of "∀x. plus(x, zero) === plus(zero, x)" PROOF {
    val refl0: SCProofStep = RightRefl(() |- s(x) === s(x), s(x) === s(x))
    val subst1 = RightSubstEq((x === plus(zero, x)) |- s(x) === s(plus(zero, x)), 0, (x, plus(zero, x)) :: Nil, LambdaTermFormula(Seq(y), s(x) === s(y)))
    val implies2 = RightImplies(() |- (x === plus(zero, x)) ==> (s(x) === s(plus(zero, x))), 1, x === plus(zero, x), s(x) === s(plus(zero, x)))
    val transform3 = RightSubstEq(
      (plus(zero, s(x)) === s(plus(zero, x))) |- (x === plus(zero, x)) ==> (s(x) === plus(zero, s(x))),
      2,
      (plus(zero, s(x)), s(plus(zero, x))) :: Nil,
      LambdaTermFormula(Seq(y), (x === plus(zero, x)) ==> (s(x) === y))
    )

    // result: ax4plusSuccessor |- 0+Sx = S(0 + x)
    val instanceAx4_4 = SCSubproof(
      instantiateForall(instantiateForallImport(ax"ax4plusSuccessor", zero), x),
      Seq(-1)
    )
    val cut5 = Cut(() |- (x === plus(zero, x)) ==> (s(x) === plus(zero, s(x))), 4, 3, plus(zero, s(x)) === s(plus(zero, x)))

    val transform6 = RightSubstEq(
      Set(plus(x, zero) === x, plus(s(x), zero) === s(x)) |- (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))),
      5,
      (plus(x, zero), x) :: (plus(s(x), zero), s(x)) :: Nil,
      LambdaTermFormula(Seq(y, z), (y === plus(zero, x)) ==> (z === plus(zero, s(x))))
    )
    val leftAnd7 = LeftAnd(
      (plus(x, zero) === x) /\ (plus(s(x), zero) === s(x)) |- (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))),
      6,
      plus(x, zero) === x,
      plus(s(x), zero) === s(x)
    )

    val instancePlusZero8 = SCSubproof(
      instantiateForallImport(ax"ax3neutral", x),
      Seq(-2)
    )
    val instancePlusZero9 = SCSubproof(
      instantiateForallImport(ax"ax3neutral", s(x)),
      Seq(-2)
    )
    val rightAnd10 = RightAnd(() |- (plus(x, zero) === x) /\ (plus(s(x), zero) === s(x)), Seq(8, 9), Seq(plus(x, zero) === x, plus(s(x), zero) === s(x)))

    val cut11 = Cut(
      () |- (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))),
      10,
      7,
      (plus(x, zero) === x) /\ (plus(s(x), zero) === s(x))
    )

    val forall12 = RightForall(
      cut11.bot.left |- forall(x, (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x)))),
      11,
      (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))),
      x
    )

    val inductionInstance: SCProofStep = InstPredSchema(
      () |- ((plus(zero, zero) === plus(zero, zero)) /\ forall(x, (plus(x, zero) === plus(zero, x)) ==> (plus(s(x), zero) === plus(zero, s(x))))) ==> forall(
        x,
        plus(x, zero) === plus(zero, x)
      ),
      -3,
      Map(sPhi -> LambdaTermFormula(Seq(x), plus(x, zero) === plus(zero, x)))
    )

    SCProof(
      applyInduction(
        SCSubproof(SCProof(RightRefl(() |- zero === zero, zero === zero))),
        SCSubproof(
          SCProof(
            IndexedSeq(refl0, subst1, implies2, transform3, instanceAx4_4, cut5, transform6, leftAnd7, instancePlusZero8, instancePlusZero9, rightAnd10, cut11, forall12),
            IndexedSeq(ax"ax4plusSuccessor", ax"ax3neutral")
          ),
          Seq(-1, -2)
        ),
        inductionInstance
      ),
      IndexedSeq(ax"ax4plusSuccessor", ax"ax3neutral", ax"ax7induction")
    )
  } using (ax"ax4plusSuccessor", ax"ax3neutral", ax"ax7induction")
  show

  THEOREM("switch successor") of "∀y. ∀x. plus(x, s(y)) === plus(s(x), y)" PROOF {
    //////////////////////////////////// Base: x + S0 = Sx + 0 ///////////////////////////////////////////////
    val base0 = {
      // x + 0 = x
      val xEqXPlusZero0 = SCSubproof(instantiateForallImport(ax"ax3neutral", x), IndexedSeq(-1))
      // Sx + 0 = Sx
      val succXEqSuccXPlusZero1 = SCSubproof(instantiateForallImport(ax"ax3neutral", s(x)), IndexedSeq(-1))
      // x + S0 = S(x + 0)
      val xPlusSuccZero2 = SCSubproof(instantiateForall(instantiateForallImport(ax"ax4plusSuccessor", x), zero), IndexedSeq(-2))

      // ------------------- x + 0 = x, Sx + 0 = Sx, x + S0 = S(x + 0) |- Sx + 0 = x + S0 ---------------------
      val succX3 = RightRefl(() |- s(x) === s(x), s(x) === s(x))
      val substEq4 = RightSubstEq(
        Set(s(x) === plus(s(x), zero), x === plus(x, zero)) |- plus(s(x), zero) === s(plus(x, zero)),
        3,
        (s(x), plus(s(x), zero)) :: (VariableTerm(x), plus(x, zero)) :: Nil,
        LambdaTermFormula(Seq(y, z), y === s(z))
      )
      val substEq5 = RightSubstEq(
        Set(s(x) === plus(s(x), zero), x === plus(x, zero), s(plus(x, zero)) === plus(x, s(zero))) |- plus(s(x), zero) === plus(x, s(zero)),
        4,
        (s(plus(x, zero)), plus(x, s(zero))) :: Nil,
        LambdaTermFormula(Seq(z), plus(s(x), zero) === z)
      )
      // -------------------------------------------------------------------------------------------------------
      val cut6 = Cut(Set(s(x) === plus(s(x), zero), x === plus(x, zero)) |- plus(s(x), zero) === plus(x, s(zero)), 2, 5, s(plus(x, zero)) === plus(x, s(zero)))
      val cut7 = Cut(x === plus(x, zero) |- plus(s(x), zero) === plus(x, s(zero)), 1, 6, s(x) === plus(s(x), zero))
      val cut8 = Cut(() |- plus(s(x), zero) === plus(x, s(zero)), 0, 7, x === plus(x, zero))
      SCSubproof(
        SCProof(
          IndexedSeq(xEqXPlusZero0, succXEqSuccXPlusZero1, xPlusSuccZero2, succX3, substEq4, substEq5, cut6, cut7, cut8),
          IndexedSeq(ax"ax3neutral", ax"ax4plusSuccessor")
        ),
        IndexedSeq(-1, -2)
      )
    }

    /////////////// Induction step: ∀y. (x + Sy === Sx + y) ==> (x + SSy === Sx + Sy) ////////////////////
    val inductionStep1 = {
      // x + SSy = S(x + Sy)
      val moveSuccessor0 = SCSubproof(instantiateForall(instantiateForallImport(ax"ax4plusSuccessor", x), s(y)), IndexedSeq(-2))

      // Sx + Sy = S(Sx + y)
      val moveSuccessor1 = SCSubproof(instantiateForall(instantiateForallImport(ax"ax4plusSuccessor", s(x)), y), IndexedSeq(-2))

      // ----------- x + SSy = S(x + Sy), x + Sy = Sx + y, S(Sx + y) = Sx + Sy |- x + SSy = Sx + Sy ------------
      val middleEq2 = RightRefl(() |- s(plus(x, s(y))) === s(plus(x, s(y))), s(plus(x, s(y))) === s(plus(x, s(y))))
      val substEq3 =
        RightSubstEq(
          Set(plus(x, s(y)) === plus(s(x), y)) |- s(plus(x, s(y))) === s(plus(s(x), y)),
          2,
          (plus(x, s(y)), plus(s(x), y)) :: Nil,
          LambdaTermFormula(Seq(z1), s(plus(x, s(y))) === s(z1))
        )
      val substEq4 =
        RightSubstEq(
          Set(plus(x, s(y)) === plus(s(x), y), plus(x, s(s(y))) === s(plus(x, s(y)))) |- plus(x, s(s(y))) === s(plus(s(x), y)),
          3,
          (plus(x, s(s(y))), s(plus(x, s(y)))) :: Nil,
          LambdaTermFormula(Seq(z1), z1 === s(plus(s(x), y)))
        )
      val substEq5 =
        RightSubstEq(
          Set(plus(x, s(s(y))) === s(plus(x, s(y))), plus(x, s(y)) === plus(s(x), y), s(plus(s(x), y)) === plus(s(x), s(y))) |- plus(x, s(s(y))) === plus(s(x), s(y)),
          4,
          (s(plus(s(x), y)), plus(s(x), s(y))) :: Nil,
          LambdaTermFormula(Seq(z1), plus(x, s(s(y))) === z1)
        )
      // -------------------------------------------------------------------------------------------------------
      val cut6 = Cut(Set(plus(x, s(y)) === plus(s(x), y), s(plus(s(x), y)) === plus(s(x), s(y))) |- plus(x, s(s(y))) === plus(s(x), s(y)), 0, 5, plus(x, s(s(y))) === s(plus(x, s(y))))
      val cut7 = Cut(plus(x, s(y)) === plus(s(x), y) |- plus(x, s(s(y))) === plus(s(x), s(y)), 1, 6, s(plus(s(x), y)) === plus(s(x), s(y)))
      val implies8 = RightImplies(() |- (plus(x, s(y)) === plus(s(x), y)) ==> (plus(x, s(s(y))) === plus(s(x), s(y))), 7, plus(x, s(y)) === plus(s(x), y), plus(x, s(s(y))) === plus(s(x), s(y)))
      val forall9 = RightForall(
        () |- forall(y, (plus(x, s(y)) === plus(s(x), y)) ==> (plus(x, s(s(y))) === plus(s(x), s(y)))),
        8,
        (plus(x, s(y)) === plus(s(x), y)) ==> (plus(x, s(s(y))) === plus(s(x), s(y))),
        y
      )
      SCSubproof(
        SCProof(
          IndexedSeq(moveSuccessor0, moveSuccessor1, middleEq2, substEq3, substEq4, substEq5, cut6, cut7, implies8, forall9),
          IndexedSeq(ax"ax3neutral", ax"ax4plusSuccessor")
        ),
        IndexedSeq(-1, -2)
      )
    }

    val inductionInstance = {
      val inductionOnY0 = Rewrite(() |- (sPhi(zero) /\ forall(y, sPhi(y) ==> sPhi(s(y)))) ==> forall(y, sPhi(y)), -1)
      val inductionInstance1 = InstPredSchema(
        () |-
          ((plus(s(x), zero) === plus(x, s(zero))) /\
            forall(y, (plus(x, s(y)) === plus(s(x), y)) ==> (plus(x, s(s(y))) === plus(s(x), s(y))))) ==>
          forall(y, plus(x, s(y)) === plus(s(x), y)),
        0,
        Map(sPhi -> LambdaTermFormula(Seq(y), plus(x, s(y)) === plus(s(x), y)))
      )
      SCSubproof(SCProof(IndexedSeq(inductionOnY0, inductionInstance1), IndexedSeq(ax"ax7induction")), Seq(-3))
    }
    val inductionApplication = applyInduction(base0, inductionStep1, inductionInstance)
    val addForall = RightForall(() |- forall(x, forall(y, plus(x, s(y)) === plus(s(x), y))), inductionApplication.size - 1, forall(y, plus(x, s(y)) === plus(s(x), y)), x)
    val proof: SCProof = Proof(
      inductionApplication :+ addForall,
      IndexedSeq(ax"ax3neutral", ax"ax4plusSuccessor", ax"ax7induction")
    )
    proof
  } using (ax"ax3neutral", ax"ax4plusSuccessor", ax"ax7induction")
  show

  THEOREM("additivity of addition") of "" PROOF {
    val base0 = SCSubproof(instantiateForallImport(thm"x + 0 = 0 + x", x), Seq(-3))
    val inductionStep1 = {
      val start0 = RightRefl(() |- plus(x, s(y)) === plus(x, s(y)), plus(x, s(y)) === plus(x, s(y)))
      val applyPlusSuccAx1 =
        RightSubstEq(plus(x, s(y)) === s(plus(x, y)) |- plus(x, s(y)) === s(plus(x, y)), 0, (plus(x, s(y)), s(plus(x, y))) :: Nil, LambdaTermFormula(Seq(z1), plus(x, s(y)) === z1))
      val applyInductionPremise2 =
        RightSubstEq(
          Set(plus(x, s(y)) === s(plus(x, y)), plus(x, y) === plus(y, x)) |- plus(x, s(y)) === s(plus(y, x)),
          1,
          (plus(x, y), plus(y, x)) :: Nil,
          LambdaTermFormula(Seq(z1), plus(x, s(y)) === s(z1))
        )
      val applyPlusSuccAx3 =
        RightSubstEq(
          Set(plus(x, s(y)) === s(plus(x, y)), plus(x, y) === plus(y, x), s(plus(y, x)) === plus(y, s(x))) |- plus(x, s(y)) === plus(y, s(x)),
          2,
          (s(plus(y, x)), plus(y, s(x))) :: Nil,
          LambdaTermFormula(Seq(z1), plus(x, s(y)) === z1)
        )
      val applySwitchSuccessor4 =
        RightSubstEq(
          Set(plus(x, s(y)) === s(plus(x, y)), plus(x, y) === plus(y, x), s(plus(y, x)) === plus(y, s(x)), plus(y, s(x)) === plus(s(y), x)) |- plus(x, s(y)) === plus(s(y), x),
          3,
          (plus(y, s(x)), plus(s(y), x)) :: Nil,
          LambdaTermFormula(Seq(z1), plus(x, s(y)) === z1)
        )

      val xPlusSYInstance5 = SCSubproof(instantiateForall(instantiateForallImport(ax"ax4plusSuccessor", x), y), Seq(-1))
      val cutXPlusSY6 = Cut(Set(plus(x, y) === plus(y, x), s(plus(y, x)) === plus(y, s(x)), plus(y, s(x)) === plus(s(y), x)) |- plus(x, s(y)) === plus(s(y), x), 5, 4, plus(x, s(y)) === s(plus(x, y)))
      val yPlusSXInstance7 = SCSubproof(instantiateForall(instantiateForallImport(ax"ax4plusSuccessor", y), x), Seq(-1))
      val cutYPlusSX8 = Cut(Set(plus(x, y) === plus(y, x), plus(y, s(x)) === plus(s(y), x)) |- plus(x, s(y)) === plus(s(y), x), 7, 6, s(plus(y, x)) === plus(y, s(x)))
      val swichSuccessorInstance9 = SCSubproof(instantiateForall(instantiateForallImport(thm"switch successor", y), x), Seq(-2))
      val cutSwitchSuccessor10 = Cut(plus(x, y) === plus(y, x) |- plus(x, s(y)) === plus(s(y), x), 9, 8, plus(y, s(x)) === plus(s(y), x))
      val rightImplies11 = RightImplies(() |- (plus(x, y) === plus(y, x)) ==> (plus(x, s(y)) === plus(s(y), x)), 10, plus(x, y) === plus(y, x), plus(x, s(y)) === plus(s(y), x))
      val forall12 = RightForall(() |- forall(y, (plus(x, y) === plus(y, x)) ==> (plus(x, s(y)) === plus(s(y), x))), 11, (plus(x, y) === plus(y, x)) ==> (plus(x, s(y)) === plus(s(y), x)), y)
      SCSubproof(
        Proof(
          IndexedSeq(
            start0,
            applyPlusSuccAx1,
            applyInductionPremise2,
            applyPlusSuccAx3,
            applySwitchSuccessor4,
            xPlusSYInstance5,
            cutXPlusSY6,
            yPlusSXInstance7,
            cutYPlusSX8,
            swichSuccessorInstance9,
            cutSwitchSuccessor10,
            rightImplies11,
            forall12
          ),
          IndexedSeq(ax"ax4plusSuccessor", thm"switch successor")
        ),
        IndexedSeq(-1, -4)
      )
    }

    val inductionInstance = {
      val inductionOnY0 = Rewrite(() |- (sPhi(zero) /\ forall(y, sPhi(y) ==> sPhi(s(y)))) ==> forall(y, sPhi(y)), -1)
      val inductionInstance1 = InstPredSchema(
        () |-
          ((plus(x, zero) === plus(zero, x)) /\
            forall(y, (plus(x, y) === plus(y, x)) ==> (plus(x, s(y)) === plus(s(y), x)))) ==>
          forall(y, plus(x, y) === plus(y, x)),
        0,
        Map(sPhi -> LambdaTermFormula(Seq(y), plus(x, y) === plus(y, x)))
      )
      SCSubproof(SCProof(IndexedSeq(inductionOnY0, inductionInstance1), IndexedSeq(ax"ax7induction")), Seq(-2))
    }
    val inductionApplication = applyInduction(base0, inductionStep1, inductionInstance)
    val addForall = RightForall(() |- forall(x, forall(y, plus(x, y) === plus(y, x))), inductionApplication.size - 1, forall(y, plus(x, y) === plus(y, x)), x)
    val proof: SCProof = Proof(
      inductionApplication :+ addForall,
      IndexedSeq(ax"ax4plusSuccessor", ax"ax7induction", thm"x + 0 = 0 + x", thm"switch successor")
    )
    proof
  } using (ax"ax4plusSuccessor", ax"ax7induction", thm"x + 0 = 0 + x", thm"switch successor")
  show
}
