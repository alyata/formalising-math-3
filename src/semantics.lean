import syntax
import typing_relation
import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products

open term type typing_relation
open category_theory category_theory.limits

variables {𝕍 con gnd : Type} {con_type : con → type gnd}

variables {𝓒 : Type} [category 𝓒] 
          [limits.has_finite_products 𝓒] [cartesian_closed 𝓒]

-- not sure why this is noncomputable
noncomputable def eval_type (M : gnd → 𝓒) : type gnd → 𝓒
| |G| := M G
| unit := ⊤_𝓒
| (A ∏ A') := (eval_type A) ⨯ (eval_type A')
| (A ⊃ A') := (eval_type A) ⟹ (eval_type A')

notation M `⟦` A `⟧` := eval_type M A

noncomputable def eval_env (M : gnd → 𝓒) : env gnd → 𝓒
| list.nil := ⊤_𝓒
| (A :: Γ) := eval_type M A ⨯ eval_env Γ

notation M `⟦` Γ `⟧` := eval_env M Γ

noncomputable def eval_has_type {Γ : env gnd} {t : term con} {A : type gnd} 
(M : gnd → 𝓒) (con_eval : Π c : con, ⊤_𝓒 ⟶ M⟦con_type c⟧) 
: (has_type con_type Γ t A) → (M⟦Γ⟧ ⟶ M⟦A⟧) :=
begin
  -- the recursion syntax outside tactic mode gives an error,
  -- so I use tactic mode for now
  intro 𝓙,
  induction 𝓙,
  case has_type.Var : Γ x A {
    -- M⟦Γ⟧ ⨯ M⟦A⟧ -π₂-> M⟦A⟧
    exact limits.prod.fst
  },
  case has_type.Var' : Γ x A A' rec rec_ret {
    -- M⟦Γ⟧ ⨯ M⟦A'⟧ -π₁-> M⟦Γ⟧ -rec_ret → M⟦A⟧
    unfold eval_env,
    exact limits.prod.snd ≫ rec_ret,
  },
  case has_type.Const : Γ c {
    -- M⟦Γ⟧ -⟨⟩-> ⊤ -con_eval-> M⟦con_type c⟧
    exact terminal.from (M⟦Γ⟧) ≫ con_eval c
  },
  case has_type.Unit : Γ {
    -- M⟦Γ⟧ -⟨⟩-> ⊤
    exact terminal.from (M⟦Γ⟧)
  },
  case has_type.Pair : Γ t t' A A' rec rec' rec_ret rec_ret' {
    unfold eval_type,
    exact prod.lift rec_ret rec_ret',
  },
  case has_type.Fst : Γ t A A' rec rec_ret {
    unfold eval_type at rec_ret,
    exact rec_ret ≫ limits.prod.fst,
  },
  case has_type.Snd : Γ t A A' rec rec_ret {
    unfold eval_type at rec_ret,
    exact rec_ret ≫ limits.prod.snd,
  },
  case has_type.Lam : Γ t A A' rec rec_ret {
    unfold eval_env at rec_ret,
    unfold eval_type,
    exact cartesian_closed.curry rec_ret
  },
  case has_type.App : Γ t t' A A' rec rec' rec_ret rec_ret' {
    unfold eval_type at rec_ret,
    exact prod.lift rec_ret' rec_ret ≫ (exp.ev (M⟦A⟧)).app (M⟦A'⟧)
  }
end