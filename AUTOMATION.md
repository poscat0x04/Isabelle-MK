# MK automation experiments

Run the theory and its regression lemmas with:

```sh
isabelle build -D . -o document=false -o timeout=30
```

`ROOT` includes `MK_Automation_Regression.thy`, so normal session builds also
check the regressions. Its 55 named lemmas use default `simp`, `simp_all`,
`auto`, or `blast`, without unfolding definitions or supplying local rules.
Keep the chosen method when changing a regression: replacing `simp` with
`blast` would test a different facility.

## Retained changes

- Membership simp rules for bounded comprehension, the empty and universal
  classes, singletons, binary intersection/union/difference, general
  intersection/union, and powers. Membership assumptions also discharge `Set`
  conditions in the simplifier.
- Safe introduction for bounded universals, subsets, intersections, and
  differences; safe elimination for bounded existentials, intersections,
  differences, and unions. Witness selection and extensionality remain unsafe.
- A branching bounded-universal elimination rule, binder congruences that
  provide membership assumptions while simplifying bodies, and simplifications
  for empty/singleton domains, existential equality witnesses, and subset bounds.
- Introduction and conditional simp rules for set construction: empty sets,
  singletons, unordered and ordered pairs, powers, unions, separation, and
  conditionals. These also help the existing pair projections and lambda
  application/domain simp rules discharge their guards.

The regressions include repeated universal/subset instantiation, class algebra,
nested constructors, and proper-class cases. In particular, power membership
and general intersection membership still require `Set(x)`; a singleton of a
proper class is empty and is itself a set.

## Incremental results

The original working tree built successfully. Before the membership changes,
15 of the first 18 regression lemmas failed. All 18 passed after adding the
specialized rules. The expanded quantifier/subset batch exceeded a 120-second
session timeout before its changes and passed afterward. The final constructor
batch exceeded a 30-second timeout before registering the construction rules.
After those changes, the full session passed in about five seconds on this
machine, including startup (about two seconds for the session itself).
These are individual build observations, not a statistical benchmark.

Two broader experiments were reverted: making unrestricted `comprehension` a
default simp rule disrupted existing inverse/composition proofs, and making
comprehension elimination eager disrupted the composition proof. In that first
pass the original proofs were kept intact. Use `simp add: comprehension` for explicit expansion;
`SetE`, generic subclass sethood, and replacement are also left explicit.

## Shortening existing proofs

A second pass shortened 29 existing lemmas and added 13 supporting lemmas.
`MK.thy` is over 200 lines shorter overall. Representative changes, counting
the complete lemma declarations and proofs:

| Lemma | Before | After |
| --- | ---: | ---: |
| `Lambda_fun` | 21 lines | 4 lines |
| `Lambda_ap` | 21 | 4 |
| `separation` | 52 | 13 |
| `inv_involute` | 22 | 4 |
| `compose_assoc` | 27 | 2 |

The supporting lemmas expose guarded lambda membership/ranges, function
application, conditional membership, and inverse/composition membership.
`Rel_eqI` reduces equality of relations to membership of ordered pairs. It is
invoked explicitly; lambda, inverse, and composition relation facts are
introduction rules. Function and lambda membership simp rules retain the
sethood assumptions needed for pair injectivity.

Both introduction orders for bounded existentials are available, allowing
the predicate to identify a witness before checking its domain. Application
membership (`ap_mem`) remains explicit to avoid encouraging general membership
search to invent functions. Function extensionality keeps a short calculation
through lambdas rather than asking automatic search to discover that argument.

Composition proofs use `cong: conj_cong` locally so the simplifier can use `Set`
guards while descending under existential binders. This reduced the composition
membership proof from roughly 12 seconds in a diagnostic run to a small part of
a four-second full build. The final session, including all 55 regressions,
passed with `-o document=false -o timeout=30` (about two seconds for the session).
