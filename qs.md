- i dont understand LeftImplies and LeftIff rules
- `simpl` in lisa using theorems?
- no (inductive) recursion?

---

- Why we say `The(z)` for, for instance, `secondInPairSingleton` but it is not needed for `firstInPair`. Is it when we do set comprehension?
- is there some pretty printer for theorems? Scala syntax is not very readable
- proofs are VERY fragile upon definitions, automation is needed?
- `->` vs `:=` in substitutions?
- why tautology works only on `have` and not `thenHave`?
- is there some unification? Do I have to always exactly specify the substitutions?

---

- Substitution doesnt work if there are non-free variables involved?

```scala
val sub = have(P(x) <=> Q(x)) subproof { sorry }
// works
have(P(x)) subproof { sorry }
thenHave(Q(x)) by Substitution.ApplyRules(
	sub
)
// doesn't
have(∀(x, P(x))) subproof { sorry }
thenHave(∀(x, Q(x))) by Substitution.ApplyRules(
	sub
)
```

- when doing substitution when recalling a theorem I have to name the variable exactly. Can i just refer to that name without creating a variable?
