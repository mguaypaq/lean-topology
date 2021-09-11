import tactic
import data.set.basic
import .topology

section fiber_product

variables {E B B' : Type} (π : E → B) (f : B' → B)

@[reducible]
def fiber_product : Type := {pair : B' × E // f pair.fst = π pair.snd}
@[simp] def fiber_product.fst : fiber_product π f → B' := λ x, x.val.fst
@[simp] def fiber_product.snd : fiber_product π f → E := λ x, x.val.snd
infix `×f`:110 := fiber_product

lemma fiber_product.sound :
  f ∘ fiber_product.fst π f = π ∘ fiber_product.snd π f :=
begin
  ext ⟨_, h⟩, exact h,
end

@[simp]
def fiber_product.exact.map {Z : Type} (πZ : Z → B') (fZ : Z → E)
  (h : f ∘ πZ = π ∘ fZ) : Z → π ×f f :=
λ z, ⟨⟨πZ z, fZ z⟩, congr_fun h z⟩

lemma fiber_product.exact.prop (Z : Type) (πZ : Z → B') (fZ : Z → E)
  (h : f ∘ πZ = π ∘ fZ) :
  fiber_product.fst _ _ ∘ fiber_product.exact.map _ _ _ _ h = πZ ∧
  fiber_product.snd _ _ ∘ fiber_product.exact.map _ _ _ _ h = fZ :=
begin
  split; ext; refl,
end

lemma fiber_product.universal (Z : Type) (πZ : Z → B') (fZ : Z → E)
  (h : f ∘ πZ = π ∘ fZ) (g : Z → π ×f f)
  (hg : fiber_product.fst π f ∘ g = πZ ∧ fiber_product.snd π f ∘ g = fZ) :
  g = fiber_product.exact.map _ _ _ _ h :=
begin
  ext,
    change (g x).val.fst = πZ x, rw ← hg.1, refl,
    change (g x).val.snd = fZ x, rw ← hg.2, refl,
end

/-
Annoying technical thing:

If π = ρ and f = g, then the types `fiber_product π f` and
`fiber_product ρ g` are obviously not equal. I don't even know if they
are defeq. So, I wrote the lemma `fiber_product.ext` below which maps between
fiber products of equal functions.

This is useful for when we have `h : π ∘ φ = π'` and so on.
-/


def fiber_product.ext
  (pi : E → B) (eff : B' → B) (pi_eq : pi = π) (eff_eq : eff = f) :
  π ×f f → pi ×f eff :=
  subtype.map id begin intros a h, rwa [pi_eq, eff_eq] end

lemma fiber_product.ext_app
  (pi : E → B) (eff : B' → B) (pi_eq : pi = π) (eff_eq : eff = f)
  (x : π ×f f) :
    fiber_product.ext π f pi eff pi_eq eff_eq x =
    ⟨x.val, begin rw [pi_eq, eff_eq], exact x.prop, end⟩ := rfl

-- "Composition of pullbacks along the base":
-- The following are canonically isomorphic:
--   1. the pullback of π along (f ∘ f')
--   2. the pullback of (the pullback of π along f) along f'
-- but they are not *equal* :
--    #1 is a subtype of B'' × F, whereas
--    #2 is a subtype of B'' × (fiber_product π f).
-- Definitionally these are:
--   1. {pair : B'' × F // (f ∘ f') pair.fst = π pair.snd}
--   2. {pair : B'' × α // f' pair.fst = pullback.fst π f pair.snd}
--      where α is 
--      fiber_product π f := {pair' : B' × F // f pair'.fst = π pair'.snd }.

variables {B'' : Type} (f' : B'' → B')

def fiber_product.comp_base :
  (fiber_product.fst π f) ×f f' ≃ π ×f (f ∘ f') :=
{
  to_fun :=
    fiber_product.exact.map π (f ∘ f')
      (fiber_product.fst _ f')
      (fiber_product.snd π f ∘ fiber_product.snd _ f')
      (by rw [function.comp.assoc, ←function.comp.assoc π,
              fiber_product.sound, ←fiber_product.sound π]),
  inv_fun :=
    let π'' := fiber_product.exact.map π f _
               (fiber_product.snd π (f ∘ f'))
               (by rw ← fiber_product.sound π)
    in fiber_product.exact.map _ f' _ π''
       (by rw (fiber_product.exact.prop _ _ _ _ _ _).1),
  left_inv := begin rintro ⟨⟨b'', ⟨⟨b', v⟩, h1⟩⟩, h2⟩,
                    simp, exact h2, end,
  right_inv := begin rintro ⟨⟨b'', e⟩, h⟩, refl, end }

section cts_fiber_product
variables [topology E] [topology B] [topology B'] [topology B'']

-- The topology on a fiber product is the subspace topology from E × B.
--instance fiber_product_topology : topology (π ×f f) := subtype_topology _

/-
Let's prove that all the maps in fiber product diagrams are continuous:
  -- the two projections,
  -- the map from the universal property.

Note: (fiber_product.fst π f) is cts even if π and/or f are not!
This is because it is the restriction of B' × E → B'.

It's convenient to also prove continuity of the composite map
  --  fiber_product π f → B
We give two different proofs (fiber_product.sound.cts and .cts') by going
around the square the two ways. These require either (h : cts π) or (h : cts f).
-/

lemma fiber_product.fst.cts : cts (fiber_product.fst π f) :=
  cts_of_comp _ _ coe_cts prod_fst_cts

lemma fiber_product.snd.cts : cts (fiber_product.snd π f) :=
  cts_of_comp _ _ coe_cts prod_snd_cts

lemma fiber_product.sound.cts
  (hf : cts f) : cts (f ∘ fiber_product.fst π f) :=
  cts_of_comp _ _ (fiber_product.fst.cts π f) hf
  
lemma fiber_product.sound.cts'
  (hπ : cts π) : cts (π ∘ fiber_product.snd π f) :=
  cts_of_comp _ _ (fiber_product.snd.cts π f) hπ

lemma fiber_product.exact.map.cts {Z : Type} [topology Z] 
  (πZ : Z → B') (fZ : Z → E) (πZ_cts : cts πZ) (fZ_cts : cts fZ)
  (h : f ∘ πZ = π ∘ fZ) :
  cts (fiber_product.exact.map π f πZ fZ h) :=
begin
  apply restrict_cod_cts,
  exact (cts_map_to_prod _).mpr ⟨πZ_cts, fZ_cts⟩,
end

lemma fiber_product.ext.cts
  (pi : E → B) (eff : B' → B) (pi_eq : pi = π) (eff_eq : eff = f) :
  cts (fiber_product.ext π f pi eff pi_eq eff_eq) :=
  subtype_map_cts cts.id

lemma fiber_product.comp_base.cts
  (hπ : cts π) (hf : cts f) (hf' : cts f') :
  cts (fiber_product.comp_base π f f').to_fun :=
begin
  apply fiber_product.exact.map.cts,
  apply fiber_product.fst.cts,
  simp,
  apply cts_of_comp, apply cts_of_comp, apply cts_of_comp,
  exact coe_cts, exact prod_snd_cts, exact coe_cts, exact prod_snd_cts,
end

end cts_fiber_product

end fiber_product
