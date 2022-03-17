
namespace type


@[derive(decidable_eq)]
inductive type (gnd : Type) : Type
| Gnd  : gnd → type
| Unit : type
| Prod : type → type → type
| Fun  : type → type → type

notation `|` G `|` := type.Gnd G
notation `unit`   := type.Unit
infixl ` ∏ `:65 := type.Prod
infixr ` ⊃ `:66 := type.Fun

end type

namespace term

open type

/- λ-calculus terms with a locally nameless representation (using De-Bruijn 
indices) so we do not need the notion of α-equivalence. -/

@[derive(decidable_eq)]
inductive term (gnd con : Type) : Type
| Const : con → term
| Var   : ℕ → term
| Unit  : term
| Pair  : term → term → term
| Fst   : term → term
| Snd   : term → term
| Abs   : type gnd → term → term
| App   : term → term → term

notation `|` c `|`                := term.Const c
notation `⌈` n `⌉`                := term.Var n
notation `⟪⟫`                     := term.Unit
notation `⟪` t1 `, ` t2 `⟫`       := term.Pair t1 t2
notation `fst` t                  := term.Fst t 
notation `snd` t                  := term.Snd t 
notation `Λ ` A `. ` t             := term.Abs A t
infixl    ` ⬝ `:65                 := term.App

variables {gnd con : Type}

/-- A term is bounded to `fv` and `n` iff all the free variables that appear 
are contained in `fv` and all the bound variables that occur free refer to a 
De-Bruijn level less than `n`. -/
def bounded_to : ℕ → term gnd con → Prop
| bound |c| := true
| bound ⌈n⌉ := n < bound
| bound ⟪⟫  := true
| bound ⟪t1, t2⟫ := (bounded_to bound t1) ∧ (bounded_to bound t2)
| bound (fst t) := bounded_to bound t
| bound (snd t) := bounded_to bound t
| bound (Λ _. t) := bounded_to (bound + 1) t
| bound (t1 ⬝ t2) := (bounded_to bound t1) ∧ (bounded_to bound t2)

def substitute (N : term gnd con) : ℕ → term gnd con → term gnd con
| x |c|   := |c|
| x ⌈y⌉ := if (x = y) then N else ⌈y⌉
| x ⟪⟫ := ⟪⟫
| x ⟪t1, t2⟫ := ⟪substitute x t1, substitute x t2⟫
| x (fst t1) := fst (substitute x t1)
| x (snd t1) := snd (substitute x t1)
| x (Λ A. M) := Λ A. (substitute (x+ 1) M)
| x (P ⬝ Q) := (substitute x P) ⬝ (substitute x Q)

end term