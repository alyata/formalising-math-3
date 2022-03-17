import syntax
import tactic

namespace typing_relation

open term type

variables {con gnd : Type} (con_type : con → type gnd)

def env (gnd : Type) := list (type gnd)

inductive has_type : env gnd → term gnd con → type gnd → Type
| Var  : ∀ {Γ A},
-----------------------
has_type (A :: Γ) ⌈0⌉ A

| Var' : ∀ {Γ x A A'}, 
has_type Γ ⌈x⌉ A
-------------------------
→ has_type (A' :: Γ) ⌈x+1⌉ A

| Const : ∀ {Γ c},
-------------------------------
has_type Γ (|c|) (con_type c)

| Unit : ∀ {Γ},
--------------------
has_type Γ ⟪⟫ unit

| Pair : ∀ {Γ t t' A A'},
has_type Γ t A → has_type Γ t' A'
-------------------------------------
→ has_type Γ ⟪t, t'⟫ (A ∏ A')

| Fst : ∀ {Γ t A A'},
has_type Γ t (A ∏ A')
------------------------
→ has_type Γ (fst t) A

| Snd : ∀ {Γ t A A'},
has_type Γ t (A ∏ A')
-------------------------
→ has_type Γ (snd t) A'

| Lam : ∀ {Γ t A A'},
has_type (A :: Γ) t A'
---------------------------------------------
→ has_type Γ (Λ A. t) (A ⊃ A')

| App : ∀ {Γ t t' A A'},
has_type Γ t (A ⊃ A') → has_type Γ t' A
---------------------------------------------
→ has_type Γ (t ⬝ t') A'

theorem type_unicity {Γ : env gnd} {t : term gnd con} 
{A1 A2 : type gnd} {con_type : con → type gnd} 
(h1 : has_type con_type Γ t A1) (h2 : has_type con_type Γ t A2)
: A1 = A2 :=
begin
  with_cases {induction t generalizing Γ A1 A2; cases h1; cases h2},
  case term.Const { refl },
  case term.Unit { refl },
  case term.Pair : t1 t2 ih1 ih2 Γ A1 A2 h1t1 h1t2 B1 B2 h2t1 h2t2 {
    simp only,
    split,
    exact ih1 h1t1 h2t1,
    exact ih2 h1t2 h2t2
  },
  case term.Fst : t ih Γ A1 A2 B1 h1 B2 h2 {
    specialize ih h1 h2,
    simp only at ih,
    exact ih.left
  },
  case term.Snd : t ih Γ A1 A2 B1 h1 B2 h2 {
    specialize ih h1 h2,
    simp only at ih,
    exact ih.right
  },
  case term.Abs : B t ih Γ A1 h1 A2 h2 {
    specialize ih h1 h2,
    simp only [eq_self_iff_true, true_and],
    exact ih
  },
  case term.App : t1 t2 ih1 ih2 Γ A1 A2 B1 h1t2 h1t1 B2 h2t2 h2t1 {
    specialize ih1 h1t1 h2t1,
    simp only at ih1,
    exact ih1.right,
  },
  case term.Var has_type.Var { refl },
  case term.Var has_type.Var' : A1 A2 Γ x A' h1 h2 {
    with_cases { induction x generalizing Γ; cases h1; cases h2 },
    case nat.zero { refl },
    case nat.succ : x ih Γ A' h1 h2 { exact ih h1 h2 }
  }
end 

theorem deriv_unicity {Γ : env gnd} {t : term gnd con} 
{A : type gnd} {con_type : con → type gnd} 
(h1 h2 : has_type con_type Γ t A) : h1 = h2 :=
begin
  with_cases {induction t generalizing A Γ; cases h1; cases h2},

  case term.Const { refl },
  case term.Unit { refl },
  case term.Pair : t1 t2 ih1 ih2 Γ A B h1t1 h1t2 h2t1 h2t2 {
    rw ih1 h1t1 h2t1,
    rw ih2 h1t2 h2t2
  },
  case term.Fst : t ih A Γ B1 h1 B2 h2 {
    have := type_unicity h1 h2,
    simp only [eq_self_iff_true, true_and] at this,
    subst this,
    rw ih h1 h2,
  },
  case term.Snd : t ih A Γ B1 h1 B2 h2 {
    have := type_unicity h1 h2,
    simp only [eq_self_iff_true, and_true] at this,
    subst this,
    rw ih h1 h2,
  },
  case term.Abs : A t ih Γ B h1 h2 {
    rw ih h1 h2
  },
  case term.App : t1 t2 ih1 ih2 B Γ A1 h1t2 h1t1 A2 h2t2 h2t1 {
    have := type_unicity h1t2 h2t2,
    subst this,
    rw ih1 h1t1 h2t1,
    rw ih2 h1t2 h2t2,
  },
  case term.Var has_type.Var : A Γ { refl },
  case term.Var has_type.Var' : A Γ x A' h1 h2 {
    with_cases { induction x generalizing Γ; cases h1; cases h2 },
    case nat.zero { refl },
    case nat.succ : x ih Γ A' h1 h2 {
      specialize ih h1 h2,
      simp only at ih,
      rw ih
    }
  }
end

end typing_relation