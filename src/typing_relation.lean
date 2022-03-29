import syntax
import tactic
import data.list
import data.list.sigma
import data.subtype
import tactic.induction

namespace typing_relation

open term type

variables {gnd con fv : Type} [fvar fv] [const con gnd]

-- Tried alist, it got messy
def env (gnd fv : Type) := list (Σ (_ : fv), type gnd)
instance : has_mem (Σ (_ : fv), type gnd) (env gnd fv) := list.has_mem

inductive ok : env gnd fv → Prop
| Nil  : ok []
| Cons : ∀ {Γ x A}, ok Γ → x ∉ Γ.keys → ok (⟨x, A⟩ :: Γ)

theorem nodupkeys_of_ok {Γ : env gnd fv} (hΓ : ok Γ) : Γ.nodupkeys :=
begin
  induction hΓ,
  case ok.Nil { exact list.nodupkeys_nil },
  case ok.Cons : Γ x A hΓ hx ih {
    simp only [list.nodupkeys_cons],
    exact ⟨hx, ih⟩
  }
end

-- This has to be a Type, since we interpret the structure of derivations
-- into morphisms in a category for the semantics. Making it Prop would make it
-- impossible to pattern match on the structure of the derivations, since proofs
-- are erased.
inductive has_type : env gnd fv → term gnd con fv → type gnd → Type

| Fvar  : ∀ {Γ : env gnd fv} {x : fv} {A : type gnd},
ok (⟨x, A⟩ :: Γ)
------------------------------
→ has_type (⟨x, A⟩ :: Γ) ⌊x⌋ A

| Fvar' : ∀ {Γ : env gnd fv} {x y : fv} {A A' : type gnd},
y ∉ Γ.keys → x ≠ y → has_type Γ ⌊x⌋ A
-------------------------------------
→ has_type (⟨y, A'⟩ :: Γ) ⌊x⌋ A

| Const : ∀ {Γ c},
ok Γ
-------------------------------
→ has_type Γ (|c|) (const.type_of c)

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

-- Since has_type is a Type not Prop, this should really be Π not ∀, but it's
-- helpful to think of it as like a Prop with proof-relevance.
| Lam : ∀ {Γ : env gnd fv} {t A A'},
(∀ x ∉ free_vars t ∪ Γ.keys.to_finset, has_type (⟨x, A⟩ :: Γ) (open_var x 0 t) A')
--------------------------------------------------------------------------------
→ has_type Γ (Λ A. t) (A ⊃ A')

| App : ∀ {Γ t t' A A'},
has_type Γ t (A ⊃ A') → has_type Γ t' A
---------------------------------------------
→ has_type Γ (t ⬝ t') A'

notation Γ ` ⊩ ` t ` ∷ ` A := has_type Γ t A

variables {Γ : env gnd fv} (t t1 t2 : lc_term gnd con fv) {A A1 A2 B : type gnd}
          {x : fv}

lemma mem_of_has_type_fv (h : Γ ⊩ (⌊x⌋ : term gnd con fv) ∷ A)
: sigma.mk x A ∈ Γ :=
begin
  induction' h,
  { simp },
  { simp, right, exact ih }
end

lemma ok_of_has_type {t : term gnd con fv} (h : Γ ⊩ t ∷ A) 
: ok Γ :=
begin
  induction' h,
  case typing_relation.has_type.Fvar
  { exact h },
  case typing_relation.has_type.Fvar' : Γ x y A A' h h_1 h_2 ih
  { apply ok.Cons, exact ih, exact h },
  case typing_relation.has_type.Const : Γ c
  { exact h },
  case typing_relation.has_type.Unit
  { exact h },
  case typing_relation.has_type.Pair : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { exact ih1 },
  case typing_relation.has_type.Fst : Γ t_1 A A' h ih
  { exact ih },
  case typing_relation.has_type.Snd : Γ t_1 A A' h ih
  { exact ih },
  case typing_relation.has_type.Lam : Γ t1 A B h ih
  { set x := fvar.fresh (free_vars t1 ∪ Γ.keys.to_finset),
    have hfresh := fvar.hfresh (free_vars t1 ∪ Γ.keys.to_finset),
    specialize @ih x hfresh,
    cases' ih,
    exact ih
  },
  case typing_relation.has_type.App : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { exact ih1 }
end

theorem type_unicity (h1 : Γ ⊩ t.val ∷ A1) (h2 : Γ ⊩ t.val ∷ A2)
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
    set x := fvar.fresh (free_vars t ∪ Γ.keys.to_finset),
    have hfresh := fvar.hfresh (free_vars t ∪ Γ.keys.to_finset),
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
    have hnodup := nodupkeys_of_ok (ok_of_has_type h1),
    exact hnodup.eq_of_mk_mem (mem_of_has_type_fv h1) (mem_of_has_type_fv h2)
  }
end 

theorem deriv_unicity
(h1 h2 : Γ ⊩ t.val ∷ A) : h1 = h2 :=
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
    have := type_unicity ⟨t, hlc⟩ h1 h2,
    simp only [eq_self_iff_true, true_and] at this,
    subst this,
    rw ih h1 h2,
  },
  case locally_closed.Snd : _ t hlc ih A Γ B1 h1 B2 h2 {
    have := type_unicity ⟨t, hlc⟩ h1 h2,
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
    have := type_unicity ⟨t2, hlc2⟩ h1t2 h2t2,
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
      simp only [not_or_distrib, list.keys_cons, list.mem_cons_iff] at hy,
      exact ih hy.right h1 hy.right h2, 
    },
  }
end

lemma weakening {t : term gnd con fv} (hx : x ∉ free_vars t ∪ Γ.keys.to_finset)
(h : Γ ⊩ t ∷ A) : (⟨x, B⟩::Γ) ⊩ t ∷ A :=
begin
  induction' h generalizing Γ t A,
  case typing_relation.has_type.Fvar : Γ x_1 A h
  { simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
               finset.union_insert, finset.mem_insert, finset.mem_union,
               list.mem_to_finset] at hx,
    apply has_type.Fvar',
    { simp only [not_or_distrib, list.keys_cons, list.mem_cons_iff], 
      exact ⟨hx.left, hx.right.right⟩ },
    { symmetry, exact hx.left },
    exact has_type.Fvar h
  },
  case typing_relation.has_type.Fvar' : Γ x_1 y A A' h h_1 h_2 ih
  { simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
               finset.union_insert, finset.mem_insert, finset.mem_union,
               list.mem_to_finset, free_vars, finset.not_mem_singleton] at hx,
    apply has_type.Fvar',
    { simp only [not_or_distrib, list.keys_cons, list.mem_cons_iff], 
      exact ⟨hx.left, hx.right.right⟩ },
    { symmetry, exact hx.right.left },
    apply has_type.Fvar',
    { exact h }, { exact h_1 },
    exact h_2
  },
  case typing_relation.has_type.Const : Γ c h
  { apply has_type.Const,
    apply ok.Cons,
    exact h,
    simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
              finset.union_insert, finset.mem_insert, finset.mem_union,
              list.mem_to_finset] at hx,
    exact hx.right,
  },
  case typing_relation.has_type.Unit : Γ h
  { apply has_type.Unit,
    apply ok.Cons,
    exact h,
    simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
              finset.union_insert, finset.mem_insert, finset.mem_union,
              list.mem_to_finset] at hx,
    exact hx.right,
  },
  case typing_relation.has_type.Pair : Γ t1 t2 A1 A2 h1 h2 ih1 ih2
  { simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
               finset.union_insert, finset.mem_insert, finset.mem_union,
               list.mem_to_finset, free_vars, finset.not_mem_singleton] at hx,
    apply has_type.Pair,
    { apply ih1, 
      simp only [not_or_distrib, finset.mem_union, list.mem_to_finset], 
      exact ⟨hx.left.left, hx.right⟩
    },
    { apply ih2,
      simp only [not_or_distrib, finset.mem_union, list.mem_to_finset], 
      exact ⟨hx.left.right, hx.right⟩
    }
  },
  case typing_relation.has_type.Fst : Γ t A A' h ih
  { apply has_type.Fst, exact ih hx },
  case typing_relation.has_type.Snd : Γ t A A_1 h ih
  { apply has_type.Snd, exact ih hx },
  case typing_relation.has_type.Lam : Γ t A A_1 h ih
  { apply has_type.Lam, intros x1 hx1, sorry /-need exchange lemma here -/ },
  case typing_relation.has_type.App : Γ t1 t2 A B h1 h2 ih1 ih2
  { simp only [not_or_distrib, list.keys_cons, list.to_finset_cons, 
               finset.union_insert, finset.mem_insert, finset.mem_union,
               list.mem_to_finset, free_vars, finset.not_mem_singleton] at hx,
    apply has_type.App,
    { apply ih1, 
      simp only [not_or_distrib, finset.mem_union, list.mem_to_finset], 
      exact ⟨hx.left.left, hx.right⟩
    },
    { apply ih2,
      simp only [not_or_distrib, finset.mem_union, list.mem_to_finset], 
      exact ⟨hx.left.right, hx.right⟩
    } 
  },
end

lemma subst_preserves_type (hx : x # t2.val)
(h1 : has_type (⟨x, A1⟩::Γ) t2.val A2) (h2 : has_type Γ t1.val A1)
: has_type Γ (subst t1.val x t2.val) A2 :=
begin
  cases t1,
  cases t2,
  simp only [subtype.coe_mk] at h1 h2 ⊢,
  induction t2_val,
  case term.term.Const : t2
  { simp [subst] at ⊢,
    cases' h1, 
    apply has_type.Const,
    cases' h,
    exact h
  },
  case term.term.Bvar : t
  {
    sorry
  },
  case term.term.Fvar : t
  { admit },
  case term.term.Unit
  { admit },
  case term.term.Pair : t_ᾰ t_ᾰ_1 t_ih_ᾰ t_ih_ᾰ_1
  { admit },
  case term.term.Fst : t_ᾰ t_ih
  { admit },
  case term.term.Snd : t_ᾰ t_ih
  { admit },
  case term.term.Abs : t_ᾰ t_ᾰ_1 t_ih
  { admit },
  case term.term.App : t_ᾰ t_ᾰ_1 t_ih_ᾰ t_ih_ᾰ_1
  { admit }
end

end typing_relation