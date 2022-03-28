import syntax
import tactic
import data.list
import data.list.sigma
import data.subtype
import tactic.induction

namespace typing_relation

open term type

variables {con gnd fvar : Type} [decidable_eq fvar] 

-- Tried alist, got messy
def env (gnd fvar : Type) := list (Σ (_ : fvar), type gnd)
instance : has_mem (Σ (_ : fvar), type gnd) (env gnd fvar) := list.has_mem

inductive ok : env gnd fvar → Prop
| Nil  : ok []
| Cons : ∀ {Γ x A}, ok Γ → x ∉ Γ.keys → ok (⟨x, A⟩ :: Γ)

theorem nodupkeys_of_ok {Γ : env gnd fvar} (hΓ : ok Γ) : Γ.nodupkeys :=
begin
  induction hΓ,
  case ok.Nil { exact list.nodupkeys_nil },
  case ok.Cons : Γ x A hΓ hx ih {
    simp only [list.nodupkeys_cons],
    exact ⟨hx, ih⟩
  }
end

inductive has_type (con_type : con → type gnd) 
: env gnd fvar → term gnd con fvar → type gnd → Type

| Fvar  : ∀ {Γ : env gnd fvar} {x : fvar} {A : type gnd},
ok (⟨x, A⟩ :: Γ)
------------------------------
→ has_type (⟨x, A⟩ :: Γ) ⌊x⌋ A

| Fvar' : ∀ {Γ : env gnd fvar} {x y : fvar} {A A' : type gnd},
y ∉ Γ.keys → x ≠ y → has_type Γ ⌊x⌋ A
-------------------------------------
→ has_type (⟨y, A'⟩ :: Γ) ⌊x⌋ A

| Const : ∀ {Γ c},
ok Γ
-------------------------------
→ has_type Γ (|c|) (con_type c)

| Unit : ∀ {Γ},
ok Γ
--------------------
→ has_type Γ ⟪⟫ unit

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

| Lam : ∀ {Γ : env gnd fvar} {t A A'},
(∀ x ∉ free_vars t ∪ Γ.keys.to_finset, has_type (⟨x, A⟩ :: Γ) (open_var x 0 t) A')
--------------------------------------------------------------------------------
→ has_type Γ (Λ A. t) (A ⊃ A')

| App : ∀ {Γ t t' A A'},
has_type Γ t (A ⊃ A') → has_type Γ t' A
---------------------------------------------
→ has_type Γ (t ⬝ t') A'

variables {con_type : con → type gnd} {Γ : env gnd fvar} 
(t : lc_term gnd con fvar) {A A1 A2 : type gnd}

lemma mem_of_has_type_fvar {x : fvar} (h : has_type con_type Γ ⌊x⌋ A)
: sigma.mk x A ∈ Γ :=
begin
  induction' h,
  { simp },
  { simp, right, exact ih }
end

lemma ok_of_has_type {t : term gnd con fvar}
(fresh : finset fvar → fvar) (hfresh : ∀ S, fresh S ∉ S) 
(h : has_type con_type Γ t A) : ok Γ :=
begin
  induction' h fixing fresh hfresh,
  case typing_relation.has_type.Fvar : Γ x A h
  { exact h },
  case typing_relation.has_type.Fvar' : Γ x y A A' h h_1 h_2 ih
  { apply ok.Cons, exact ih, exact h },
  case typing_relation.has_type.Const : Γ c
  { exact h },
  case typing_relation.has_type.Unit : Γ
  { exact h },
  case typing_relation.has_type.Pair : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { exact ih1 },
  case typing_relation.has_type.Fst : Γ t_1 A A' h ih
  { exact ih },
  case typing_relation.has_type.Snd : Γ t_1 A A' h ih
  { exact ih },
  case typing_relation.has_type.Lam : Γ t1 A B h ih
  { set x := fresh (free_vars t1 ∪ Γ.keys.to_finset),
    specialize hfresh (free_vars t1 ∪ Γ.keys.to_finset),
    specialize @ih x hfresh,
    cases' ih,
    exact ih
  },
  case typing_relation.has_type.App : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { exact ih1 }
end

theorem type_unicity 
(fresh : finset fvar → fvar) (hfresh : ∀ S, fresh S ∉ S) 
(h1 : has_type con_type Γ ↑t A1) (h2 : has_type con_type Γ ↑t A2)
: A1 = A2 :=
begin
  rcases t with ⟨t, ht⟩,
  with_cases {induction ht generalizing Γ A1 A2; cases h1; cases h2},
  case locally_closed.Const { refl },
  case locally_closed.Unit { refl },
  case locally_closed.Pair
  : _ t1 t2 hlc1 hlc2 ih1 ih2 Γ A1 A2 h1t1 h1t2 B1 B2 h2t1 h2t2 {
    simp only,
    split,
    exact ih1 h1t1 h2t1,
    exact ih2 h1t2 h2t2
  },
  case locally_closed.Fst : _ t hlc ih Γ A1 A2 B1 h1 B2 h2 {
    specialize ih h1 h2,
    simp only at ih,
    exact ih.left
  },
  case locally_closed.Snd : _ t hlc ih Γ A1 A2 B1 h1 B2 h2 {
    specialize ih h1 h2,
    simp only at ih,
    exact ih.right
  },
  case locally_closed.Abs : _ B t hlc ih Γ A1 h1 A2 h2 {
    simp only [eq_self_iff_true, true_and],
    set x := fresh (free_vars t ∪ Γ.keys.to_finset),
    specialize @hfresh (free_vars t ∪ Γ.keys.to_finset),
    specialize h1 x hfresh,
    specialize h2 x hfresh,
    simp only [not_or_distrib, finset.mem_union, list.mem_to_finset] at hfresh,
    exact ih x hfresh.left h1 h2,
  },
  case locally_closed.App 
  : _ t1 t2 hlc1 hlc2 ih1 ih2 Γ A1 A2 B1 h1t2 h1t1 B2 h2t2 h2t1 {
    specialize ih1 h1t1 h2t1,
    simp only at ih1,
    exact ih1.right,
  },
  case has_type.Fvar has_type.Fvar { refl },
  case has_type.Fvar has_type.Fvar' { contradiction },
  case has_type.Fvar' has_type.Fvar { contradiction },
  case has_type.Fvar' has_type.Fvar' : _ x A1 A2 Γ y A' hy hneq h1 _ _ h2 { 
    have hnodup := nodupkeys_of_ok (ok_of_has_type fresh hfresh h1),
    exact hnodup.eq_of_mk_mem (mem_of_has_type_fvar h1) (mem_of_has_type_fvar h2)
  }
end 

theorem deriv_unicity
{A : type gnd} {con_type : con → type gnd} 
(fresh : finset fvar → fvar) (hfresh : ∀ S, fresh S ∉ S)
(h1 h2 : has_type con_type Γ ↑t A) : h1 = h2 :=
begin
  cases' t with t ht,
  with_cases {induction ht generalizing Γ A; cases h1; cases h2},

  case locally_closed.Const { refl },
  case locally_closed.Unit { refl },
  case locally_closed.Pair 
  : _ t1 t2 hlc1 hlc2 ih1 ih2 Γ A B h1t1 h1t2 h2t1 h2t2 {
    rw ih1 h1t1 h2t1,
    rw ih2 h1t2 h2t2
  },
  case locally_closed.Fst : _ t hlc ih A Γ B1 h1 B2 h2 {
    have := type_unicity ⟨t, hlc⟩ fresh hfresh h1 h2,
    simp only [eq_self_iff_true, true_and] at this,
    subst this,
    rw ih h1 h2,
  },
  case locally_closed.Snd : _ t hlc ih A Γ B1 h1 B2 h2 {
    have := type_unicity ⟨t, hlc⟩ fresh hfresh h1 h2,
    simp only [eq_self_iff_true, and_true] at this,
    subst this,
    rw ih h1 h2,
  },
  case locally_closed.Abs : _ A t hlc ih Γ B h1 h2 {
    simp only,
    ext x hx,
    -- need to keep two versions of hx, one as it is (that appears in the goal),
    -- one simplified to use as lemma
    have hx_simp := hx,
    simp only [not_or_distrib, finset.mem_union, list.mem_to_finset] at hx_simp,
    exact ih x hx_simp.left (h1 x hx) (h2 x hx),
  },
  case locally_closed.App
  : _ t1 t2 hlc1 hlc2 ih1 ih2 B Γ A1 h1t2 h1t1 A2 h2t2 h2t1 {
    have := type_unicity ⟨t2, hlc2⟩ fresh hfresh h1t2 h2t2,
    subst this,
    rw ih1 h1t1 h2t1,
    rw ih2 h1t2 h2t2,
  },
  case has_type.Fvar has_type.Fvar { refl },
  case has_type.Fvar has_type.Fvar' { contradiction },
  case has_type.Fvar' has_type.Fvar { contradiction },
  case has_type.Fvar' has_type.Fvar' : t x A1 Γ y A2 hy hneq h1 hy' hneq' h2 {
    simp only,
    with_cases { induction' Γ fixing *; cases h1; cases h2 },
    case has_type.Fvar has_type.Fvar
    { refl },
    case has_type.Fvar has_type.Fvar'
    { contradiction },
    case has_type.Fvar' has_type.Fvar
    { contradiction },
    case has_type.Fvar' has_type.Fvar' : Γ ih x' A' hy _ h1x' h1neqx' h1 h2x' h2neqx' h2
    { simp only,
      simp [not_or_distrib] at hy,
      exact ih hy.right h1 hy.right h2, 
    },
  }
end

end typing_relation