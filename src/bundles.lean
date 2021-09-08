import tactic
import .topology
import .gluing

section fiber_space

variables {E E' B : Type} (π' : E' → B) (φ : E → E')

def res_base (U : set B) :
  φ ⁻¹' (π' ⁻¹' U) → π' ⁻¹' U :=
  subtype.map φ (by simp)

@[simp]
lemma res_base_def (U : set B)
  (a : E) (ha : a ∈ φ ⁻¹' (π' ⁻¹' U)) :
  res_base _ _ U ⟨a, ha⟩ = ⟨φ a, ha⟩ := rfl

lemma from_sub_res_image_of_to_sub
  (U : set B) (V : set E) :
  from_sub _ ((res_base π' φ U) '' (to_sub _ V)) =
    (π' ⁻¹' U) ∩ (φ '' V) :=
begin
  ext e', simp, split,
  rintro ⟨e'', he'', ⟨e, he⟩, he12⟩, rw he12 at *,
  exact ⟨he'', ⟨e, he.1, he.2.2⟩⟩,
  rintro ⟨he', e, he1, he2⟩, use e', split, exact he', use e,
  simp [he2], exact ⟨he1, he'⟩,
end

lemma from_sub_res_preimage_of_to_sub
  (U : set B) (V : set E') :
  from_sub _ ((res_base π' φ U) ⁻¹' (to_sub _ V)) = 
    φ ⁻¹' ((π' ⁻¹' U) ∩ V) :=
begin
  unfold from_sub, unfold to_sub, unfold res_base,
  ext e, simp, split,
  rintro ⟨x, hx⟩, rw ← hx.2.2, exact ⟨hx.1, hx.2.1⟩,
  intro h, use e, simp, exact h,
end

lemma res_base_inj_of_inj
  (hφ_inj : function.injective φ) (U : set B) : 
  function.injective (res_base π' φ U) :=
begin
  apply subtype.map_injective, exact hφ_inj,
end

lemma res_base_surj_of_surj
  (hφ_surj : function.surjective φ) (U : set B) : 
  function.surjective (res_base π' φ U) :=
begin
  rintro ⟨x, hx⟩, obtain ⟨y, hy⟩ := hφ_surj x,
  use y, simp, rwa hy,
  simp, exact hy,
end

lemma res_base_bij_of_bij
  (hφ_bij : function.bijective φ) (U : set B) : 
  function.bijective (res_base π' φ U) :=
begin
  split,
    apply res_base_inj_of_inj _ _ hφ_bij.1,
    apply res_base_surj_of_surj _ _ hφ_bij.2,
end


variables {I : Type} (U : cover I B)

lemma fiber_map_inj_iff_cover_inj :
  function.injective φ ↔
  ∀ i, function.injective (res_base π' φ (U i)) :=
begin
  split,
    intros hφ_inj i, apply res_base_inj_of_inj, exact hφ_inj,
  intros hφ_inj_cover e1 e2 he,
  obtain ⟨i, hi⟩ := U.hx (π' (φ e1)),
  specialize @hφ_inj_cover i ⟨e1, hi⟩ ⟨e2, by rwa he at hi⟩,
  simp at hφ_inj_cover, exact hφ_inj_cover he,
end

lemma fiber_map_surj_iff_cover_surj :
  function.surjective φ ↔
  ∀ i, function.surjective (res_base π' φ (U i)) :=
begin
  split,
    intros hφ_surj i, apply res_base_surj_of_surj, exact hφ_surj,
  intro hφ_surj_cover, intro e',
  obtain ⟨i, hi⟩ := U.hx (π' e'),
  obtain ⟨⟨a, ha⟩, ha'⟩ := hφ_surj_cover i ⟨e', hi⟩,
  use a, simp at ha', exact ha',
end

lemma fiber_map_bij_iff_cover_bij :
  function.bijective φ ↔ 
  ∀ i, function.bijective (res_base π' φ (U i)) :=
begin
  unfold function.bijective,
  rw forall_and_distrib,
  rw ← fiber_map_inj_iff_cover_inj,
  rw ← fiber_map_surj_iff_cover_surj,
end

section fiber_bundle

open topology

variables [topology B] [topology E] [topology E']
  {J : Type} (V : open_cover J B)

lemma res_base_cts_of_cts
  (hπ'_cts : cts π') (hφ_cts : cts φ) (U ∈ opens B) :
  cts (res_base π' φ U) :=
  subtype_map_cts hφ_cts

lemma fiber_map_cts_iff_cover_cts
  (hπ_cts : cts (π' ∘ φ)) (hπ'_cts : cts π') :
  cts φ ↔
  ∀ j, cts (res_base π' φ (V j)) :=
begin
  split,
    intros hφ_cts j,
    apply res_base_cts_of_cts _ _ hπ'_cts hφ_cts _ (V.hopen j),
  intros hφ_cts_cover,
  rw cts_iff_ptwise_cts, intros e W hW heW, simp,
  obtain ⟨j, hj⟩ := V.hx (π' (φ e)),
  use φ ⁻¹' (π' ⁻¹' (V j) ∩ W),
  split, -- proof of openness
    specialize hφ_cts_cover j (to_sub _ W),
    rw to_sub_open_iff at hφ_cts_cover,
    specialize hφ_cts_cover ⟨W, hW, rfl⟩,
    rw from_sub_open_iff at hφ_cts_cover,
    rwa ← from_sub_res_preimage_of_to_sub,
    rw ←set.preimage_comp,
    apply hπ_cts, exact V.hopen j,
  split, simp, simp, exact ⟨hj, heW⟩,
end

lemma res_base_open_map_of_open_map
  (hπ_cts : cts (π' ∘ φ)) (hπ'_cts : cts π')
  (hφ_open : open_map φ)
  (U ∈ opens B) :
  open_map (res_base π' φ U) :=
begin
  apply subtype_map_open, exact hφ_open,
  change ((π' ∘ φ) ⁻¹' U ∈ opens E), apply hπ_cts, exact ‹U ∈ opens B›,
end

lemma fiber_map_open_map_iff_res_open_map
  (hπ_cts : cts (π' ∘ φ)) (hπ'_cts : cts π') :
  open_map φ ↔
  ∀ j, open_map (res_base π' φ (V j)) :=
begin
  split,
    intros hφ_open j,
    apply res_base_open_map_of_open_map _ _ hπ_cts hπ'_cts hφ_open _ (V.hopen j),
  intros hφ_open_map W hW,
  rw subset_open_iff_open_cover (pullback_open_cover π' hπ'_cts V),
  intro j, change π' ⁻¹' (V j) ∩ φ '' W ∈ opens E',
  specialize hφ_open_map j (to_sub _ W),
  rw to_sub_open_iff at hφ_open_map,
  specialize hφ_open_map ⟨W, hW, rfl⟩,
  rw from_sub_open_iff at hφ_open_map,
  rwa ← from_sub_res_image_of_to_sub,
  apply hπ'_cts, exact V.hopen j,
end

lemma res_base_homeo_of_homeo
  (hπ_cts : cts (π' ∘ φ)) (hπ'_cts : cts π')
  (hφ_homeo : homeo φ)
  (U ∈ opens B) :
  homeo (res_base π' φ U) :=
begin
  rw homeo_iff at *,
  split,
    exact res_base_cts_of_cts _ _ hπ'_cts hφ_homeo.1 U ‹U ∈ opens B›,
  split,
    exact res_base_bij_of_bij _ _ hφ_homeo.2.1 U,
    exact res_base_open_map_of_open_map _ _ hπ_cts hπ'_cts hφ_homeo.2.2 U ‹U ∈ opens B›,
end

lemma fiber_map_homeo_iff_res_homeo
  (hπ_cts : cts (π' ∘ φ)) (hπ'_cts : cts π') :
  homeo φ ↔
  ∀ j, homeo (res_base π' φ (V j)) :=
begin
  split, intros hφ_homeo j,
    exact res_base_homeo_of_homeo _ _ hπ_cts hπ'_cts hφ_homeo (V j) (V.hopen j),
  intro hφ_homeo,
  rw [homeo_iff,
      fiber_map_cts_iff_cover_cts _ _ V hπ_cts hπ'_cts,
      fiber_map_bij_iff_cover_bij _ _ V.to_cover,
      fiber_map_open_map_iff_res_open_map _ _ V hπ_cts hπ'_cts,
      ← forall_and_distrib, ← forall_and_distrib],
  intro j, specialize hφ_homeo j, rwa homeo_iff at hφ_homeo,
end

end fiber_bundle
end fiber_space

section fiber_product

variables {E B B' : Type} (π : E → B) (f : B' → B)

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
  to_fun := fiber_product.exact.map π (f ∘ f')
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
  right_inv := begin rintro ⟨⟨b'', e⟩, h⟩, simp, end }

section cts_fiber_product
variables [topology E] [topology B] [topology B'] [topology B'']

-- The topology on a fiber product is the subspace topology from E × B.
instance fiber_product_topology :
  topology (π ×f f) := subtype_topology _

/-
Let's prove that all the maps in fiber product diagrams are continuous:
  -- the two projections,
  -- the map from the universal property.

Note: (fiber_product.fst π f) is cts even if π and/or f are not!
This is because it is the restriction of B' × E → B'.

It's convenient to also prove continuity of the composite map
  --  fiber_product π f → B
We give two different proofs (fiber_product.sound.cts and .cts') by going
around the square the two ways. These require either (cts π) or (cts f).
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

section fiber_bundle

/-

Bundles.

Goal: Show that trivializations pull back.

We distinguish between:
  1. *trivial bundles* : these are bundles of the form
      prod.fst : B × fiber → B
  2. *trivializations of bundles* : given π : E → B, this is the data of
      φ  : equiv (B × fiber) E,
      hφ : π ∘ φ = prod.fst

These aren't the same thing of course. (In real life, this occurs when a bundle
can be trivialized in many ways. Think of picking a basis of a vector space.
For trivial bundles (1), the choice is already made. Otherwise it's data.)

Warning: The pullback of a trivial bundle B × fiber along f : B' → B is trivializable,
in fact *canonically* trivializable (we will write down a natural trivialization).
But it is not *definitionally* trivial. This is because it has the form

      {(b, f b, v)} ⊆ B' × B × fiber

rather than being B' × fiber, with the definition we give in terms of fiber products.
It is (almost) defeq to (graph of f) × fiber.

Our approach:

a) Define bundles, bundle maps and functorial pullbacks of bundle maps
   (in particular of equivalences).
b) Define trivial bundle
c) Define trivialization of bundle (:= equivalence of the bundle with a trivial bundle)
d) Construct a *canonical* trivialization of the pullback of a trivial bundle.
   (This uses the notion of graph of a function.)
e) Combine (a) and (d) to "pull back trivializations". 🎉
-/

-- Bundles and bundle maps.

structure bundle (B : Type) := 
  (space : Type)
  (π : space → B)

instance bundle_to_proj (B : Type) : has_coe_to_fun (bundle B) :=
{ F   := λ E, E.space → B, 
  coe := λ E, E.π }

@[ext]
structure bundle_map {B : Type} (E F : bundle B) :=
  (map : E.space → F.space)
  (h : F.π ∘ map = E.π)
infix `→→`:110 := bundle_map

instance bundle_map_to_fn {B : Type} (E F : bundle B) : has_coe_to_fun (E →→ F) :=
{ F   := λ φ, E.space → F.space, 
  coe := λ φ, φ.map }

def bundle_map.id {B : Type} (E : bundle B) : E →→ E :=
{ map := id,
  h   := function.comp.right_id E.π, }

def bundle_map.comp {B : Type} {E F G : bundle B}
  (φ' : F →→ G) (φ : E →→ F) : E →→ G :=
{ map := φ'.map ∘ φ.map,
  h   := by rw [← function.comp.assoc, φ'.h, φ.h], }
infix `∘∘`:110 := bundle_map.comp

@[simp]
lemma bundle_map.comp.assoc {B : Type} {E F G H : bundle B}
  (φ'' : G →→ H) (φ' : F →→ G) (φ : E →→ F) :
  (φ'' ∘∘ φ') ∘∘ φ = φ'' ∘∘ (φ' ∘∘ φ) := rfl

@[simp]
lemma bundle_map.left_id {B : Type} {E F : bundle B} (φ : bundle_map E F) :
  (bundle_map.id F) ∘∘ φ = φ :=
begin
  ext x, refl,
end

@[simp]
lemma bundle_map.right_id {B : Type} {E F : bundle B} (φ : bundle_map E F) :
  φ ∘∘ (bundle_map.id E) = φ :=
begin
  ext x, refl,
end

structure bundle_equiv {B : Type} (E F : bundle B) :=
  (to_bundle_map  : E →→ F)
  (inv_bundle_map : F →→ E)
  (left_inv       : inv_bundle_map ∘∘ to_bundle_map = bundle_map.id E)
  (right_inv      : to_bundle_map ∘∘ inv_bundle_map = bundle_map.id F)
infix `≃≃`:100 := bundle_equiv

def bundle_equiv.mk' {B : Type} {E F : bundle B}
  (φ : equiv E.space F.space)
  (hφ : F.π ∘ φ.to_fun = E.π)
  (hφ_inv : E.π ∘ φ.inv_fun = F.π) : E ≃≃ F :=
  { to_bundle_map  := ⟨φ.to_fun, hφ⟩,
    inv_bundle_map := ⟨φ.inv_fun, hφ_inv⟩,
    left_inv       := begin ext e, exact φ.left_inv e, end,
    right_inv      := begin ext e, exact φ.right_inv e, end }

def bundle_equiv.trans {B : Type} {E F G : bundle B}
  (φ : E ≃≃ F) (φ' : F ≃≃ G) : E ≃≃ G :=
  { to_bundle_map  := φ'.to_bundle_map ∘∘ φ.to_bundle_map,
    inv_bundle_map := φ.inv_bundle_map ∘∘ φ'.inv_bundle_map,
    left_inv       := by rw [bundle_map.comp.assoc,
                             ← bundle_map.comp.assoc φ'.inv_bundle_map,
                             φ'.left_inv,
                             bundle_map.left_id,
                             φ.left_inv],
    right_inv      := by rw [bundle_map.comp.assoc,
                             ← bundle_map.comp.assoc φ.to_bundle_map,
                             φ.right_inv,
                             bundle_map.left_id,
                             φ'.right_inv], }

section pullback
-- Pullbacks. Closely related to fiber products.

@[reducible]
def pullback_bundle {B' B : Type} (f : B' → B) (E : bundle B) : bundle B' :=
{ space := fiber_product E.π f,
  π := fiber_product.fst E.π f }
infix `**`:110 := pullback_bundle

def pullback_map {B' B : Type} (f : B' → B) {E F : bundle B} (φ : E →→ F) :
  (f ** E) →→ (f ** F) :=
{ map := fiber_product.exact.map F.π f (f ** E).π (φ.map ∘ (fiber_product.snd E.π f))
         begin rw [← function.comp.assoc F.π, φ.h, ← fiber_product.sound], end,
  h := begin ext ⟨⟨e', b'⟩, h⟩, refl, end,
}
infix `↖*`:110 := pullback_map

--variables {B' B : Type} (f : B' → B) {E F G : bundle B} (φ' : F →→ G) (φ : E →→ F)

@[simp]
lemma pullback_map.def {B' B : Type} (f : B' → B) {E F G : bundle B}
  (φ' : F →→ G) (φ : E →→ F) {b' : B'} {e : E.space} {h : f b' = E.π e} :
  (f ↖* φ) ⟨(b', e), h⟩ =
    ⟨(b', φ e), begin change f b' = (F.π ∘ φ.map) e, rw φ.h, exact h, end⟩ := rfl

lemma pullback_map.comp {B' B : Type} (f : B' → B) {E F G : bundle B}
  (φ' : F →→ G) (φ : E →→ F) :
  (f ↖* φ') ∘∘ (f ↖* φ) = f ↖* (φ' ∘∘ φ) := rfl

lemma pullback_map.of_id {B' B : Type} (f : B' → B) (E : bundle B) :
  (f ↖* (bundle_map.id E)) = (bundle_map.id (f ** E)) :=
begin
  ext ⟨⟨e, b'⟩, h⟩, refl, refl,
end

def pullback_bundle_equiv {B' B : Type} (f : B' → B) {E F : bundle B}
  (φ : E ≃≃ F) : (f ** E) ≃≃ (f ** F) :=
{ to_bundle_map  := f ↖* φ.to_bundle_map,
  inv_bundle_map := f ↖* φ.inv_bundle_map,
  left_inv       := by rw [pullback_map.comp,
                           φ.left_inv,
                           pullback_map.of_id],
  right_inv      := by rw [pullback_map.comp,
                           φ.right_inv,
                           pullback_map.of_id], }
infix `↖≃`:110 := pullback_bundle_equiv

def pullback_comp {B'' B' B : Type} (g : B'' → B') (f : B' → B) (E : bundle B) :
  g ** (f ** E) ≃≃ (f ∘ g) ** E :=
  @bundle_equiv.mk' B'' (g ** (f ** E)) ((f ∘ g) ** E)
  (fiber_product.comp_base E.π f g)
  rfl rfl

end pullback

section trivial_bundle
-- Trivial bundles

@[reducible] def trivial_bundle (B fiber : Type) : bundle B := 
  { space := B × fiber, 
    π     := prod.fst }
infix `××`:110 := trivial_bundle

@[reducible]
def fn_graph {X Y : Type} (f : X → Y) := {pair : X × Y // f pair.fst = pair.snd}

def domain_equiv_graph {X Y : Type} (f : X → Y) :
  equiv X (fn_graph f) :=
  { to_fun := (λ x, ⟨⟨x, f x⟩, rfl⟩),
    inv_fun := (λ ⟨⟨x, y⟩, h⟩, x),
    left_inv := λ x, rfl,
    right_inv := λ ⟨⟨x, y⟩, h⟩, begin simp, exact ⟨rfl, h⟩, end,}

def prod_equiv_right {X X' : Type} (φ : equiv X X') (Y : Type) : equiv (X × Y) (X' × Y) :=
  { to_fun := prod.map φ id,
    inv_fun := prod.map φ.inv_fun id,
    left_inv := λ _, by simp,
    right_inv := λ _, by simp, }

def graph_equiv_pullback_of_trivial {B B' : Type} (fiber : Type) (f : B' → B) :
  equiv ((fn_graph f) ×× fiber).space (f ** (B ×× fiber)).space :=
  { to_fun := λ ⟨⟨⟨x, y⟩, h⟩, v⟩, ⟨⟨x, y, v⟩, h⟩,
    inv_fun := λ ⟨⟨x, y, v⟩, h⟩, ⟨⟨⟨x, y⟩, h⟩, v⟩,
    left_inv := λ ⟨⟨⟨x, y⟩, h⟩, v⟩, rfl,
    right_inv := λ ⟨⟨x, y, v⟩, h⟩, rfl }

end trivial_bundle

section cts_bundle

lemma domain_equiv_graph.cts {X Y : Type} [topology X] [topology Y]
  {f : X → Y} (hf : cts f) : cts (domain_equiv_graph f).to_fun :=
begin
  apply restrict_cod_cts,
  rw cts_map_to_prod,
  exact ⟨cts.id, hf⟩,
end

lemma domain_equiv_graph.inv_cts {X Y : Type} [topology X] [topology Y]
  {f : X → Y} (hf : cts f) : cts (domain_equiv_graph f).inv_fun :=
begin
  have : (domain_equiv_graph f).inv_fun = (prod.fst ∘ (coe : fn_graph f → X × Y)),
    ext ⟨⟨x, y⟩, h⟩, refl,
  rw this,
  apply cts_of_comp _ _ coe_cts prod_fst_cts,
end

-- This seems annoying.
lemma graph_equiv_pullback_of_trivial.cts
  {B B' : Type} [topology B] [topology B']
  {fiber : Type} [topology fiber] {f : B' → B} (hf : cts f) :
  cts (graph_equiv_pullback_of_trivial fiber f).to_fun :=
begin
  sorry,
end

-- This too.
lemma graph_equiv_pullback_of_trivial.inv_cts
  {B B' : Type} [topology B] [topology B']
  {fiber : Type} [topology fiber] {f : B' → B} (hf : cts f) :
  cts (graph_equiv_pullback_of_trivial fiber f).inv_fun :=
begin
  sorry,
end

end cts_bundle


section trivialization
-- Trivializations.

def trivialization {B : Type} (E : bundle B) (fiber : Type) := (B ×× fiber) ≃≃ E

-- Trivializing the pullback of a trivial bundle along any map.
-- This has to be done "by hand".
def trivialization_of_pullback_of_trivial {B B' : Type} (fiber : Type) (f : B' → B) :
  trivialization (f ** (B ×× fiber)) fiber :=
  bundle_equiv.mk'
    (equiv.trans (prod_equiv_right (domain_equiv_graph f) fiber)
                 (graph_equiv_pullback_of_trivial fiber f))
    rfl
    begin ext ⟨⟨b', b, v⟩, h⟩, refl, end

-- Pullback of a *trivialization* along any map.
def trivialization.pullback {B B' : Type} (E : bundle B) (fiber : Type)
  (f : B' → B) (triv : trivialization E fiber) :
  trivialization (f ** E) fiber :=
  bundle_equiv.trans
    (trivialization_of_pullback_of_trivial fiber f) (f ↖≃ triv)

end trivialization

section locally_trivial_fiber_bundle

variables {B : Type} (E : bundle B) (fiber : Type)
  [topology B] [topology E.space] [topology fiber]
  {I : Type} (U : open_cover I B)

-- 🎉 🎉 🎉 --
structure local_trivialization (h : cts E.π) :=
  (triv      : ∀ i, trivialization ((coe : U i → B) ** E) fiber)
  (htriv     : ∀ i, cts (triv i).to_bundle_map)
  (htriv_inv : ∀ i, cts (triv i).inv_bundle_map)

end locally_trivial_fiber_bundle

end fiber_bundle