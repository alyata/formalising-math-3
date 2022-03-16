import syntax

namespace typing_relation

open term type

variables {con gnd : Type} (con_type : con → type gnd)

def env (gnd : Type) := list (type gnd)

inductive has_type : env gnd → term con → type gnd → Type
| Var  : ∀ {Γ x A}, 
-----------------------
has_type (A :: Γ) ⌈x⌉ A

| Var' : ∀ {Γ x A A'}, 
has_type Γ x A
-------------------------
→ has_type (A' :: Γ) x A

| Const : ∀ {Γ c},
-------------------------------
has_type Γ (|c|) (con_type c)

| Unit : ∀ {Γ},
--------------------
has_type Γ () unit

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
→ has_type Γ (Λ t) (A ⊃ A')

| App : ∀ {Γ t t' A A'},
has_type Γ t (A ⊃ A') → has_type Γ t' A
---------------------------------------------
→ has_type Γ (t ⬝ t') A'

end typing_relation