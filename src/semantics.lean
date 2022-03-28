import syntax
import typing_relation
import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products

open term type typing_relation
open category_theory category_theory.limits

variables {con gnd fvar : Type} [decidable_eq fvar] 
variables {con_type : con → type gnd}

variables {𝓒 : Type} [category 𝓒] 
          [limits.has_finite_products 𝓒] [cartesian_closed 𝓒]

-- not sure why this is noncomputable
noncomputable def eval_type (M : gnd → 𝓒) : type gnd → 𝓒
| |G| := M G
| unit := ⊤_𝓒
| (A ∏ A') := (eval_type A) ⨯ (eval_type A')
| (A ⊃ A') := (eval_type A) ⟹ (eval_type A')

notation M `⟦` A `⟧` := eval_type M A

noncomputable def eval_env (M : gnd → 𝓒) : env gnd fvar → 𝓒
| [] := ⊤_𝓒
| (⟨x, A⟩ :: Γ) := eval_type M A ⨯ eval_env Γ

notation M `⟦` Γ `⟧` := eval_env M Γ

noncomputable def eval_has_type
(fresh : finset fvar → fvar) (hfresh : ∀ S, fresh S ∉ S)
(M : gnd → 𝓒) (con_eval : Π c : con, ⊤_𝓒 ⟶ M⟦con_type c⟧)
: Π {Γ : env gnd fvar} {t A}, (has_type con_type Γ t A) → (M⟦Γ⟧ ⟶ M⟦A⟧) :=
-- | (⟨_, A⟩ :: Γ) ⌊x⌋ _ (has_type.Fvar _) := limits.prod.fst
-- | (⟨y, A'⟩ :: Γ) ⌊x⌋ A (has_type.Fvar' _ _ rec) :=
-- by {unfold eval_env, exact (limits.prod.snd ≫ eval_has_type rec)}
-- | Γ |c| A (has_type.Const) := terminal.from (M⟦Γ⟧) ≫ con_eval c
-- | Γ ⟪⟫ unit has_type.Unit := terminal.from (M⟦Γ⟧)
-- | Γ ⟪t1, t2⟫ (A ∏ B) (has_type.Pair rec1 rec2) := 
-- by {unfold eval_type, exact prod.lift (eval_has_type rec1) (eval_has_type rec2)}
-- | Γ (fst t) A (has_type.Fst rec) := 
-- eval_has_type rec ≫ by { unfold eval_type, exact limits.prod.fst}
-- | Γ (snd t) B (has_type.Snd rec) :=
-- eval_has_type rec ≫ by { unfold eval_type, exact limits.prod.snd}
-- | Γ (Λ A. t) (_ ⊃ B) (has_type.Lam rec) := 
-- by {
--   set x := fresh (free_vars t ∪ (list.keys Γ).to_finset),
--   specialize hfresh (free_vars t ∪ (list.keys Γ).to_finset),
--   have rec_ret := eval_has_type (rec x hfresh), 
-- unfold eval_type, unfold eval_env at rec_ret,
-- exact cartesian_closed.curry rec_ret}
-- | Γ (t1 ⬝ t2) A1 (@has_type.App _ _ _ _ _ _ _ _ A2 _ rec1 rec2) :=
-- by {
--   have rec_ret1 := eval_has_type rec1, unfold eval_type at rec_ret1,
--   have rec_ret2 := eval_has_type rec2,
--   exact prod.lift rec_ret2 rec_ret1 ≫ (exp.ev (M⟦A2⟧)).app (M⟦A1⟧)
-- }

begin
  -- the recursion syntax outside tactic mode gives an error,
  -- so I use tactic mode for now
  intros Γ t A 𝓙,
  induction 𝓙,
  case has_type.Fvar : Γ x A {
    -- M⟦Γ⟧ ⨯ M⟦A⟧ -π₂-> M⟦A⟧
    exact limits.prod.fst
  },
  case has_type.Fvar' : Γ x y A A' _ _ rec rec_ret {
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
    set x := fresh (free_vars t ∪ (list.keys Γ).to_finset),
    specialize hfresh (free_vars t ∪ (list.keys Γ).to_finset),
    specialize rec_ret x hfresh,
    unfold eval_env at rec_ret,
    unfold eval_type,
    exact cartesian_closed.curry rec_ret
  },
  case has_type.App : Γ t t' A A' rec rec' rec_ret rec_ret' {
    unfold eval_type at rec_ret,
    exact prod.lift rec_ret' rec_ret ≫ (exp.ev (M⟦A⟧)).app (M⟦A'⟧)
  }
end