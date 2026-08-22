/-!
# Strong normalization of a relation

`SN r a` says every `r`-sequence starting at `a` is finite. Both STLC variants define exactly
this inductive over their own `Step` (`Stlc/DeBruijn/Reducibility.lean`,
`Stlc/Named/Typing/Normalization.lean`) and `TypeSystem.StronglyNormalizing` asks for it of an
abstract `Tm`, so it belongs beside `RTC` rather than in any one of them — the same reasoning
that put the closures in `Closure.lean`.

## Why an inductive and not `Acc`

`SN r a` is `Acc (fun x y => r y x) a`: accessibility bounds a term's chain of *predecessors*,
so strong normalization is accessibility under the *reversed* relation. Stating it directly says
what is meant, and it means a proof never has to be read through a flip — `SN.intro` takes
"every reduct is `SN`", which is how every proof of it actually goes, and `induction h` gives
that hypothesis without a coercion in the way.

It is deliberately **not** `WellFounded (fun x y => r y x)`. That asserts termination for every
element of `α`, which is a different and much stronger claim: a typed language normalizes its
*well-typed* terms while its term type still holds divergent ones, so a well-foundedness field
could not be discharged by anyone. `Stlc.Named.omega_not_sn` is the concrete witness.
-/

universe u

namespace LambdaLab

variable {α : Type u} {r : α → α → Prop} {a b : α}

/-- **`a` is strongly normalizing under `r`**: no infinite `r`-sequence starts at `a`.

Read the constructor as the definition: `a` is `SN` exactly when every `b` it relates to is. -/
inductive SN {α : Type u} (r : α → α → Prop) : α → Prop where
  | intro {a : α} : (∀ b, r a b → SN r b) → SN r a

/-- A successor of a strongly normalizing element is strongly normalizing. -/
theorem SN.unfold : SN r a → r a b → SN r b
  | .intro h, hs => h _ hs

end LambdaLab
