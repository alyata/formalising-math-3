import syntax
import typing_relation
import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products

open term type typing_relation
open category_theory category_theory.limits

variables {con gnd fv : Type} [fvar fv] [const con gnd]

variables {π : Type} [category π] 
          [limits.has_finite_products π] [cartesian_closed π]

--noncomputable because it uses limits.has_limit, which uses classical.choice
noncomputable def eval_type (G : gnd β π) : type gnd β π :=
begin
  refine type.rec _ _ _ _,
  exact G,
  exact β€_π,
  { intros A1 A2 rec1 rec2,
    exact rec1 β¨― rec2, },
  { intros A1 A2 rec1 rec2,
    exact rec1 βΉ rec2 }
end

notation M `β¦` A `β§` := eval_type M A

noncomputable def eval_env (G : gnd β π) : env gnd fv β π :=
begin
  refine list.rec _ _,
  exact β€_π,
  { rintros β¨x, Aβ© Ξ rec,
    exact eval_type G A β¨― rec}
end

notation M `β¦` Ξ `β§` := eval_env M Ξ

structure model (gnd con π: Type) [const con gnd] 
[category π] [limits.has_finite_products π] [cartesian_closed π] :=
(G : gnd β π)
(C : Ξ  c: con, β€_π βΆ Gβ¦const.type_of cβ§)

variables {Ξ : env gnd fv} {t : term gnd con fv} {A : type gnd}

set_option pp.proofs true

noncomputable def eval_has_type
(M : model gnd con π)
: (Ξ β© t β· A) β (M.Gβ¦Ξβ§ βΆ M.Gβ¦Aβ§) :=
begin
  -- the recursion syntax outside tactic mode gives a non-wf recursion error,
  -- so I use tactic mode
  intros π,
  induction π,
  case has_type.Fvar : Ξ x A {
    -- Mβ¦Ξβ§ β¨― Mβ¦Aβ§ -Οβ-> Mβ¦Aβ§
    exact limits.prod.fst
  },
  case has_type.Fvar' : Ξ x y A A' _ _ rec rec_ret {
    -- Mβ¦Ξβ§ β¨― Mβ¦A'β§ -Οβ-> Mβ¦Ξβ§ -rec_ret β Mβ¦Aβ§
    exact limits.prod.snd β« rec_ret,
  },
  case has_type.Const : Ξ c {
    -- Mβ¦Ξβ§ -β¨β©-> β€ -M.C-> Mβ¦con_type cβ§
    exact terminal.from (M.Gβ¦Ξβ§) β« M.C c
  },
  case has_type.Unit : Ξ {
    -- Mβ¦Ξβ§ -β¨β©-> β€
    exact terminal.from (M.Gβ¦Ξβ§)
  },
  case has_type.Pair : Ξ t t' A A' rec rec' rec_ret rec_ret' {
    -- Mβ¦Ξβ§ -β¨rec_ret, rec_ret'β©-> Mβ¦A β A'β§
    exact prod.lift rec_ret rec_ret',
  },
  case has_type.Fst : Ξ t A A' rec rec_ret {
    -- Mβ¦Ξβ§ -rec_ret-> Mβ¦A β A'β§ -fst-> Mβ¦Aβ§
    exact rec_ret β« limits.prod.fst,
  },
  case has_type.Snd : Ξ t A A' rec rec_ret {
    -- Mβ¦Ξβ§ -rec_ret-> Mβ¦A β A'β§ -fst-> Mβ¦A'β§
    exact rec_ret β« limits.prod.snd,
  },
  case has_type.Abs : Ξ t A A' rec rec_ret {
    -- Mβ¦Aβ§ β¨― Mβ¦Ξβ§ -rec_ret x hfresh-> Mβ¦A'β§
    -- so Mβ¦Ξβ§ -curry (rec_ret x hfresh)-> (Mβ¦Aβ§ βΉ Mβ¦A'β§)
    set x := fvar.fresh (free_vars t βͺ (list.keys Ξ).to_finset),
    have hfresh := fvar.hfresh (free_vars t βͺ (list.keys Ξ).to_finset),
    exact cartesian_closed.curry (rec_ret x hfresh)
  },
  case has_type.App : Ξ t t' A A' rec rec' rec_ret rec_ret' {
    -- Mβ¦Ξβ§ -β¨rec_ret', rec_retβ©-> (Mβ¦Aβ§ βΉ Mβ¦A'β§) β¨― Mβ¦Aβ§ -eval-> Mβ¦A'β§
    exact prod.lift rec_ret' rec_ret β« (exp.ev (M.Gβ¦Aβ§)).app (M.Gβ¦A'β§)
  }
end

-- noncomputable def eval_has_type'
-- (M : model gnd con π) : β {Ξ : env gnd fv} {t : term gnd con fv} {A : type gnd},
-- (Ξ β© t β· A) β (M.Gβ¦Ξβ§ βΆ M.Gβ¦Aβ§)
-- | (β¨_, Aβ© :: Ξ) βxβ _ (has_type.Fvar _) := limits.prod.fst
-- | (β¨y, A'β© :: Ξ) βxβ A (has_type.Fvar' _ _ rec) :=
-- limits.prod.snd β« eval_has_type' rec
-- | Ξ |c| A (has_type.Const _) := terminal.from (M.Gβ¦Ξβ§) β« M.C c
-- | Ξ βͺβ« unit (has_type.Unit _) := terminal.from (M.Gβ¦Ξβ§)
-- | Ξ βͺt1, t2β« (A β B) (has_type.Pair rec1 rec2) := 
-- prod.lift (eval_has_type' rec1) (eval_has_type' rec2)
-- | Ξ (fst t) A (has_type.Fst rec) := 
-- eval_has_type' rec β« by { unfold eval_type, exact limits.prod.fst}
-- | Ξ (snd t) B (has_type.Snd rec) :=
-- eval_has_type' rec β« by { unfold eval_type, exact limits.prod.snd}
-- | Ξ (Ξ A. t) (_ β B) (has_type.Abs rec) := 
-- by {
--   have hfresh := fvar.hfresh (free_vars t βͺ (list.keys Ξ).to_finset),
--   set x := fvar.fresh (free_vars t βͺ (list.keys Ξ).to_finset),
--   have rec_ret := eval_has_type' (rec x hfresh),
--   exact cartesian_closed.curry rec_ret}
-- | Ξ (t1 β¬ t2) A1 (@has_type.App _ _ _ _ _ _ _ _ A2 _ rec1 rec2) :=
-- by {
--   have rec_ret1 := eval_has_type' rec1, unfold eval_type at rec_ret1,
--   have rec_ret2 := eval_has_type' rec2,
--   exact prod.lift rec_ret2 rec_ret1 β« (exp.ev (M.Gβ¦A2β§)).app (M.Gβ¦A1β§)
-- }

notation M `β¦` π `β§` := eval_has_type M π
