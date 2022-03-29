import data.set
import tactic.induction
import data.equiv.denumerable
import data.list
import data.list.sigma

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

/- λ-calculus terms with a locally nameless representation. 

The bound variables are represented by how many abstractions away the 
abstraction that bound the variable is. For example,

λx. x (λy. x y) becomes λ (bvar 0) (λ (bvar 1) (bvar 0))

so we do not need the notion of α-equivalence.

The free variables are represented by names, so we can use any type that
  1) is infinite
  2) has decidable equality (decidable_eq)
  3) has a function where given a finite set of names, generates a fresh name 
     that does not appear in the set.
ℕ is a good candidate but we just assume an arbitrary `fvar` for this 
formalisation.
-/

class fvar (α : Type) :=
[hdec : decidable_eq α]
(fresh : finset α → α)
(hfresh : ∀ S, fresh S ∉ S)

-- Notice that non-finiteness is implied by having the `fresh` function:
instance fvar_is_infinite (α : Type) [fvar α]: infinite α := { 
  not_fintype := begin
    intro hfin,
    haveI := hfin,
    have hfresh := fvar.hfresh (@finset.univ α _),
    have hnfresh := @finset.mem_univ α _ (fvar.fresh finset.univ),
    contradiction
  end
}

-- a constant has some given fixed type
class const (α : Type) (gnd : Type) :=
(type_of : α → type gnd)

@[derive(decidable_eq)]
inductive term (gnd con fv : Type) : Type
| Const : con → term
| Bvar  : ℕ → term
| Fvar  : fv → term
| Unit  : term
| Pair  : term → term → term
| Fst   : term → term
| Snd   : term → term
| Abs   : type gnd → term → term -- The bound variable is typed to ensure each 
                                 -- term has a unique type.
| App   : term → term → term

notation `|` c `|`                := term.Const c
notation `⌈` i `⌉`                := term.Bvar i
notation `⌊` x `⌋`                := term.Fvar x
notation `⟪⟫`                     := term.Unit
notation `⟪` t1 `, ` t2 `⟫`       := term.Pair t1 t2
notation `fst ` t                  := term.Fst t 
notation `snd ` t                  := term.Snd t 
notation `Λ ` A `. ` t             := term.Abs A t
infixl    ` ⬝ `:65                 := term.App

variables {gnd con fv : Type} [fvar fv] [const con gnd]
instance : decidable_eq fv := fvar.hdec

def open_term (u : term gnd con fv) 
: ℕ → term gnd con fv → term gnd con fv
| k |c| := |c|
| k ⌈i⌉ := if k = i then u else ⌈i⌉
| k ⌊x⌋ := ⌊x⌋
| k ⟪⟫  := ⟪⟫
| k ⟪t1, t2⟫ := ⟪open_term k t1, open_term k t2⟫
| k (fst t) := fst (open_term k t)
| k (snd t) := snd (open_term k t)
| k (Λ A. t) := Λ A. (open_term (k+1) t)
| k (t1 ⬝ t2) := (open_term k t1) ⬝ (open_term k t2)

def open_var (x : fv) (n : ℕ) (t : term gnd con fv) := open_term ⌊x⌋ n t

def close_var (x : fv) : ℕ → term gnd con fv → term gnd con fv 
| k |c| := |c|
| k ⌈i⌉ := ⌈i⌉
| k ⌊y⌋ := if x = y then ⌈k⌉ else ⌊y⌋
| k ⟪⟫  := ⟪⟫
| k ⟪t1, t2⟫ := ⟪close_var k t1, close_var k t2⟫
| k (fst t) := fst (close_var k t)
| k (snd t) := snd (close_var k t)
| k (Λ A. t) := Λ A. (close_var (k+1) t)
| k (t1 ⬝ t2) := (close_var k t1) ⬝ (close_var k t2)

def free_vars : term gnd con fv → finset fv
| |c| := ∅
| ⌈i⌉ := ∅
| ⌊y⌋ := {y}
| ⟪⟫  := ∅
| ⟪t1, t2⟫ := free_vars t1 ∪ free_vars t2
| (fst t) := free_vars t
| (snd t) := free_vars t
| (Λ A. t) := free_vars t
| (t1 ⬝ t2) := free_vars t1 ∪ free_vars t2

notation x ` # ` t := x ∉ free_vars t
abbreviation closed (t : term gnd con fv) := free_vars t = ∅

inductive locally_closed : finset fv → term gnd con fv → Prop
| Const : ∀ {Γ c},
----------------------
locally_closed Γ (|c|)

| Fvar : ∀ {Γ x},
x ∈ Γ
----------------------
→ locally_closed Γ ⌊x⌋

| Unit : ∀ {Γ},
-------------------
locally_closed Γ ⟪⟫

| Pair : ∀ {Γ t1 t2}, 
locally_closed Γ t1 → locally_closed Γ t2
-----------------------------------------
→ locally_closed Γ ⟪t1, t2⟫

| Fst : ∀ {Γ t},
locally_closed Γ t
--------------------------
→ locally_closed Γ (fst t)

| Snd : ∀ {Γ t},
locally_closed Γ t
------------------------
→ locally_closed Γ (snd t)

-- The locally nameless paper says this should be 
-- ∃ L : finset fv, ∀ x ∉ L, locally_closed (open_var x 0 t)
-- but in Lean3 constructor arguments can't be inside another inductive type
-- so I have to use a Γ to track the abstracted variables, which makes the
-- representation even more complicated... 
| Abs : ∀ {Γ A t},
(∀ x ∉ free_vars t ∪ Γ, locally_closed (insert x Γ) (open_var x 0 t))
-------------------------------------------------------------------------
→ locally_closed Γ (Λ A. t)

| App : ∀ {Γ t1 t2},
locally_closed Γ t1 → locally_closed Γ t2
-------------------------------------
→ locally_closed Γ (t1 ⬝ t2)

-- def locally_closed' : ℕ → term gnd con fv → Prop
-- | k |c| := true
-- | k ⌈i⌉ := i < k
-- | k ⌊y⌋ := true
-- | k ⟪⟫  := true
-- | k ⟪t1, t2⟫ := locally_closed' k t1 ∧ locally_closed' k t2
-- | k (fst t) := locally_closed' k t
-- | k (snd t) := locally_closed' k t
-- | k (Λ A. t) := locally_closed' (k + 1) t
-- | k (t1 ⬝ t2) := locally_closed' k t1 ∧ locally_closed' k t2

-- lemma lc'_succ_of_lc' (t : term gnd con fv) (k : ℕ) (h : locally_closed' k t)
-- : locally_closed' (k + 1) t :=
-- begin
--   induction' t generalizing k,
--   case term.term.Const : x
--   { triv },
--   case term.term.Bvar : n
--   { exact nat.lt_succ_of_lt h },
--   case term.term.Fvar : x
--   { triv },
--   case term.term.Unit
--   { triv },
--   case term.term.Pair : t1 t2 ih1 ih2
--   { exact ⟨ih1 k h.left, ih2 k h.right⟩ },
--   case term.term.Fst : t ih
--   { exact ih k h },
--   case term.term.Snd : t ih
--   { exact ih k h },
--   case term.term.Abs : x t ih
--   { exact ih (k+1) h, },
--   case term.term.App : t1 t2 ih1 ih2
--   { exact ⟨ih1 k h.left, ih2 k h.right⟩ }
-- end

-- lemma lc'_zero_iff_lc' (t : term gnd con fv) 
-- : locally_closed' 0 t ↔ (∀ k, locally_closed' k t) :=
-- begin
--   split, swap,
--   { intro h, exact h 0 },
--   intros h k,
--   induction' k fixing *,
--   exact h,
--   exact lc'_succ_of_lc' t k ih,
-- end

-- theorem lc_iff_lc' (t : term gnd con fv) : locally_closed t ↔ locally_closed' 0 t :=
-- begin
--   induction' t fixing *,
--   case term.term.Const : x
--   { simp only [locally_closed', iff_true], 
--     exact locally_closed.Const
--   },
--   case term.term.Bvar : n
--   { simp only [locally_closed', nat.not_lt_zero, iff_false],
--     intro h,
--     cases h
--   },
--   case term.term.Fvar : x
--   { simp only [locally_closed', iff_true],
--     exact locally_closed.Fvar 
--   },
--   case term.term.Unit
--   { simp only [locally_closed', iff_true],
--     exact locally_closed.Unit
--   },
--   case term.term.Pair : t1 t2 ih1 ih2
--   { simp only [locally_closed'], split,
--     intro h, cases' h, rw ih1 at h, rw ih2 at h_1, exact ⟨h, h_1⟩,
--     rintro ⟨h1, h2⟩, rw ←ih1 at h1, rw ←ih2 at h2, exact locally_closed.Pair h1 h2,
--   },
--   case term.term.Fst : t ih
--   { admit },
--   case term.term.Snd : t ih
--   { admit },
--   case term.term.Abs : x t ih
--   { rw lc'_zero_iff_lc' at ih ⊢, simp only [locally_closed', zero_add], split,
--     intros h k, cases' h, 
--   },
--   case term.term.App : t t_1 ih_t ih_t_1
--   { admit }
-- end 

-- abbreviation lc (t : term gnd con fv) := locally_closed (free_vars t) t

-- def lc_term (gnd con fv : Type) [fvar fv] [const con gnd]
-- := {t : term gnd con fv // lc t}
-- instance : has_lift_t (lc_term gnd con fv) (term gnd con fv)
-- := {lift := subtype.val}

-- lemma lc_subterms_of_lc_pair {t1 t2 : term gnd con fv} 
-- {t : lc_term gnd con fv} (ht : ↑t = ⟪t1, t2⟫) 
-- : (∃ (lct1 : lc_term gnd con fv), ↑lct1 = t1) ∧ 
--   (∃ (lct2 : lc_term gnd con fv), ↑lct2 = t2) :=
-- begin
--   cases' t,
--   simp at ht,
--   subst ht,
--   cases' property,
--   split,
--   exact ⟨⟨t1, property⟩, rfl⟩,
--   exact ⟨⟨t2, property_1⟩, rfl⟩,
-- end

-- lemma lc_subterms_of_lc_fst {subt : term gnd con fv}
-- {t : lc_term gnd con fv} (ht : ↑t = fst subt)
-- : ∃ (lct : lc_term gnd con fv), ↑lct = subt :=
-- begin
--   cases' t,
--   simp at ht,
--   subst ht,
--   cases' property,
--   exact ⟨⟨t, property⟩, rfl⟩,
-- end

-- lemma lc_subterms_of_lc_snd {subt : term gnd con fv}
-- {t : lc_term gnd con fv} (ht : ↑t = snd subt)
-- : ∃ (lct : lc_term gnd con fv), ↑lct = subt :=
-- begin
--   cases' t,
--   simp at ht,
--   subst ht,
--   cases' property,
--   exact ⟨⟨t, property⟩, rfl⟩,
-- end

-- lemma lc_subterms_of_lc_abs {subt : term gnd con fv}
-- {t : lc_term gnd con fv} {A : type gnd} (ht : ↑t = Λ A. subt)
-- : ∀ x # subt, ∃ (lct : lc_term gnd con fv), ↑lct = open_var x 0 subt :=
-- begin
--   intros x hx,
--   cases' t,
--   simp at ht,
--   subst ht,
--   cases' property,
--   exact ⟨⟨open_var x 0 t, property x hx⟩, rfl⟩
-- end

-- lemma lc_subterms_of_lc_app {t1 t2 : term gnd con fv} 
-- {t : lc_term gnd con fv} (ht : ↑t = t1 ⬝ t2) 
-- : (∃ (lct1 : lc_term gnd con fv), ↑lct1 = t1) ∧ 
--   (∃ (lct2 : lc_term gnd con fv), ↑lct2 = t2) :=
-- begin
--   cases' t,
--   simp at ht,
--   subst ht,
--   cases' property,
--   split,
--   exact ⟨⟨t1, property⟩, rfl⟩,
--   exact ⟨⟨t2, property_1⟩, rfl⟩,
-- end

-- def body (t : term gnd con fv) := ∀ x # t, lc (open_var x 0 t)

-- lemma lc_abs_iff_body {t : term gnd con fv} {A : type gnd}
-- : lc (Λ A. t) ↔ body t := begin
--   split,
--   { intros h, cases h, exact h_ᾰ },
--   { exact locally_closed.Abs }
-- end

def subst (u : term gnd con fv) (x : fv)
: term gnd con fv → term gnd con fv
| ⌈i⌉ := ⌈i⌉
| |c| := |c|
| ⌊y⌋ := if x = y then u else ⌊y⌋
| ⟪⟫  := ⟪⟫
| ⟪t1, t2⟫ := ⟪subst t1, subst t2⟫
| (fst t) := fst (subst t)
| (snd t) := snd (subst t)
| (Λ A. t) := Λ A. (subst t)
| (t1 ⬝ t2) := (subst t1) ⬝ (subst t2)

theorem open_term_eq_subst_of_open_var (t u : term gnd con fv) (x : fv) (n : ℕ)
(hx : x # t) : open_term u n t = subst u x (open_var x n t) :=
begin
  induction' t generalizing n,
  case term.term.Const : c
  { simp only [open_term, open_var, subst] },
  case term.term.Bvar : n
  { simp only [open_term, open_var], 
    split_ifs,
    { simp [subst], },
    { simp [subst], }
  },
  case term.term.Fvar : x_1
  { simp only [open_term, open_var, subst],
    split_ifs,
    { simp only [free_vars, finset.mem_singleton] at hx, contradiction },
    { refl } },
  case term.term.Unit
  { simp only [open_term, open_var, subst] },
  case term.term.Pair : t1 t2 ih1 ih2
  { simp only [free_vars, not_or_distrib, finset.mem_union] at hx,
    specialize ih1 n hx.left,
    specialize ih2 n hx.right,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih1 ih2,
    exact ⟨ih1, ih2⟩ 
  },
  case term.term.Fst : t ih
  { simp only [free_vars] at hx,
    specialize ih n hx,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih,
    exact ih
  },
  case term.term.Snd : t ih
  { simp only [free_vars] at hx,
    specialize ih n hx,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih,
    exact ih
  },
  case term.term.Abs : A t ih
  { simp only [free_vars] at hx,
    specialize ih (n + 1) hx,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih,
    exact ⟨rfl, ih⟩ 
  },
  case term.term.App : t1 t2 ih1 ih2
  { simp only [free_vars, not_or_distrib, finset.mem_union] at hx,
    specialize ih1 n hx.left,
    specialize ih2 n hx.right,
    simp only [open_term, open_var, subst],
    simp only [open_var] at ih1 ih2,
    exact ⟨ih1, ih2⟩
  }
end 

end term

-- def locally_closed : term gnd con fvar → Prop
-- | |c| := true
-- | ⌈i⌉ := false
-- | ⌊y⌋ := true
-- | ⟪⟫  := true
-- | ⟪t1, t2⟫ := locally_closed t1 ∧ locally_closed t2
-- | (fst t) := locally_closed t
-- | (snd t) := locally_closed t
-- | (Λ A. t) := ∃ (L : set fvar) [set.finite L], ∀ x ∈ L, 
--               locally_closed (open_var x 0 t)
-- | (t1 ⬝ t2) := (close_var k t1) ⬝ (close_var k t2)

/- A term is bounded to `fv` and `n` iff all the free variables that appear 
are contained in `fv` and all the bound variables that occur free refer to a 
De-Bruijn level less than `n`. -/
-- def bounded_to : ℕ → term gnd con → Prop
-- | bound |c| := true
-- | bound ⌈n⌉ := n < bound
-- | bound ⟪⟫  := true
-- | bound ⟪t1, t2⟫ := (bounded_to bound t1) ∧ (bounded_to bound t2)
-- | bound (fst t) := bounded_to bound t
-- | bound (snd t) := bounded_to bound t
-- | bound (Λ _. t) := bounded_to (bound + 1) t
-- | bound (t1 ⬝ t2) := (bounded_to bound t1) ∧ (bounded_to bound t2)

-- def substitute (N : term gnd con) : ℕ → term gnd con → term gnd con
-- | x |c|   := |c|
-- | x ⌈y⌉ := if (x = y) then N else ⌈y⌉
-- | x ⟪⟫ := ⟪⟫
-- | x ⟪t1, t2⟫ := ⟪substitute x t1, substitute x t2⟫
-- | x (fst t1) := fst (substitute x t1)
-- | x (snd t1) := snd (substitute x t1)
-- | x (Λ A. M) := Λ A. (substitute (x+ 1) M)
-- | x (P ⬝ Q) := (substitute x P) ⬝ (substitute x Q)
