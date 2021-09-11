import tactic
import .topology
import .gluing
import .fiber_product

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

      {(b, f b, v)} ⊆ B' × (B × fiber)

rather than being B' × fiber, with the definition we give in terms of fiber products.
It is (almost) defeq to (id ×f f) × fiber, except for being parenthesized wrong.

Our approach:

a) Define bundles, bundle maps and functorial pullbacks of bundle maps
   (in particular of equivalences).
b) Define trivial bundle
c) Define trivialization of bundle (:= equivalence to the bundle from a trivial bundle)
d) Construct a *canonical* trivialization of the pullback of a trivial bundle.
   (Method: equivalence from trivial bundles to bundles pulled back from the constant map to a point).
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

def bundle_equiv.symm {B : Type} {E F : bundle B}
  (φ : E ≃≃ F) : F ≃≃ E :=
  { to_bundle_map  := φ.inv_bundle_map,
    inv_bundle_map := φ.to_bundle_map,
    left_inv       := φ.right_inv,
    right_inv      := φ.left_inv }

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
infix `≃∘≃`:110 := bundle_equiv.trans

-- some other lemmas I've needed

def prod_equiv_right {X X' : Type} (φ : equiv X X') (Y : Type) :
  equiv (X × Y) (X' × Y) :=
  { to_fun := prod.map φ id,
    inv_fun := prod.map φ.inv_fun id,
    left_inv := λ _, by simp,
    right_inv := λ _, by simp, }

def prod_equiv_left (X : Type) {Y Y' : Type} (φ : equiv Y Y') :
  equiv (X × Y) (X × Y') :=
  { to_fun := prod.map id φ,
    inv_fun := prod.map id φ.inv_fun,
    left_inv := λ _, by simp,
    right_inv := λ _, by simp, }

section pullback
-- Pullbacks. Closely related to fiber products.

open fiber_product

@[reducible]
def pullback_bundle {B' B : Type} (f : B' → B) (E : bundle B) : bundle B' :=
{ space := E.π ×f f,
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

def trivial_equiv_pullback_from_pt (B fiber : Type) :
  B ×× fiber ≃≃ (topology.map_to_point B) ** (trivial_bundle topology.point fiber) :=
  bundle_equiv.mk'
  (equiv.trans 
    (prod_equiv_left B (prod_point_left fiber)).symm
    { to_fun    := restrict_cod id (λ b, (topology.point.is_singleton b.snd.fst).symm),
      inv_fun   := coe,
      left_inv  := begin rintro ⟨x, y⟩, refl, end,
      right_inv := begin rintro ⟨x, h⟩, refl, end }
      )
  rfl rfl

/-
@[reducible]
def fn_graph {X Y : Type} (f : X → Y) := {pair : X × Y // f pair.fst = pair.snd}

example {X Y : Type} (f : X → Y) : fn_graph f = id ×f f := rfl

def domain_equiv_graph {X Y : Type} (f : X → Y) :
  equiv X (id ×f f) :=
  { to_fun := (λ x, ⟨⟨x, f x⟩, rfl⟩),
    inv_fun := (λ ⟨⟨x, y⟩, h⟩, x),
    left_inv := λ x, rfl,
    right_inv := λ ⟨⟨x, y⟩, h⟩, begin simp, exact ⟨rfl, h⟩, end,}

@[simp]
def graph_equiv_pullback_of_trivial {B B' : Type} (fiber : Type) (f : B' → B) :
  equiv ((id ×f f) ×× fiber).space (f ** (B ×× fiber)).space :=
  { to_fun := λ x, ⟨⟨x.1.val.1, x.1.val.2, x.2⟩, x.1.prop⟩,
    --to_fun := λ ⟨⟨⟨x, y⟩, h⟩, v⟩, ⟨⟨x, y, v⟩, h⟩,
    inv_fun := λ x, ⟨⟨⟨x.val.1, x.val.2.1⟩, x.prop⟩, x.val.2.2⟩,
    --inv_fun := λ ⟨⟨x, y, v⟩, h⟩, ⟨⟨⟨x, y⟩, h⟩, v⟩,
    left_inv := λ ⟨⟨⟨x, y⟩, h⟩, v⟩, rfl,
    right_inv := λ ⟨⟨x, y, v⟩, h⟩, rfl }
-/

end trivial_bundle

section cts_bundle

/-
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
  have : (domain_equiv_graph f).inv_fun = (prod.fst ∘ (coe : (id ×f f) → X × Y)),
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
  set g : (B' × B) × fiber → B' × (B × fiber) :=
    λ x, ⟨x.1.1, x.1.2, x.2⟩ with hg,
  have key1 :
    (graph_equiv_pullback_of_trivial fiber f).to_fun =
    @restrict_cod _ _
      (g ∘ 
      (coe : (fn_graph f ×× fiber).space → (B' × B) × fiber))
      (λ (x : B' × (B × fiber)), f x.fst = x.snd.fst)
      begin rintro ⟨⟨⟨x, y⟩, h⟩, v⟩, simp, exact h, end,
    ext ⟨⟨⟨x, y⟩, h⟩, v⟩, simp, refl, refl, rw key1,
  apply restrict_cod_cts _,
  apply cts_of_comp _ g _ _,
  have : (coe : (fn_graph f ×× fiber).space → (B' × B) × fiber)
    = prod.map (@coe (fn_graph f) (B' × B) _) (@id fiber),
  ext ⟨⟨⟨x, y⟩, h⟩, v⟩, refl, refl, refl, rw this,
  
  apply prod_of_cts,
  exact coe_cts, exact cts.id,
  
  rw cts_map_to_prod, rw cts_map_to_prod,
  split, change cts (prod.fst ∘ prod.fst), exact cts_of_comp _ _ prod_fst_cts prod_fst_cts,
  split, change cts (prod.snd ∘ prod.fst), exact cts_of_comp _ _ prod_fst_cts prod_snd_cts,
  exact prod_snd_cts,
end

-- This too.
lemma graph_equiv_pullback_of_trivial.inv_cts
  {B B' : Type} [topology B] [topology B']
  {fiber : Type} [topology fiber] {f : B' → B} (hf : cts f) :
  cts (graph_equiv_pullback_of_trivial fiber f).inv_fun :=
begin
  rw cts_map_to_prod, split,
  have key1 :
    prod.fst ∘ (graph_equiv_pullback_of_trivial fiber f).inv_fun =
    @restrict_cod _ _
      ((λ x, ⟨x.1, x.2.1⟩ : B' × B × fiber → (B' × B)) ∘ 
      (coe : (f ** (B ×× fiber)).space → B' × B × fiber))
      (λ (x : B' × B), f x.fst = x.snd)
      begin rintro ⟨⟨x, y, v⟩, h⟩, simp, exact h, end,
    ext ⟨⟨x, y, v⟩, h⟩, refl, refl, rw key1,
  apply restrict_cod_cts,
  apply cts_of_comp _ _ coe_cts,
  rw cts_map_to_prod, split,
  exact prod_fst_cts,
  change cts (prod.fst ∘ prod.snd),
  exact cts_of_comp _ _ prod_snd_cts prod_fst_cts,
  
  have key2 :
    prod.snd ∘ (graph_equiv_pullback_of_trivial fiber f).inv_fun =
      ((λ x, x.2.2 : B' × B × fiber → fiber) ∘ 
      (coe : (f ** (B ×× fiber)).space → B' × B × fiber)),
    ext ⟨⟨x, y, v⟩, h⟩, refl, rw key2,
  apply cts_of_comp _ _ coe_cts,
  apply cts_of_comp _ _ prod_snd_cts prod_snd_cts,
end
-/

end cts_bundle


section trivialization
-- Trivializations.

@[reducible]
def trivialization {B : Type} (E : bundle B) (fiber : Type) := (B ×× fiber) ≃≃ E


/-
-- Trivializing the pullback of a trivial bundle along any map.
-- This has to be done "by hand".
def trivialization_of_pullback_of_trivial {B B' : Type} (fiber : Type) (f : B' → B) :
  trivialization (f ** (B ×× fiber)) fiber :=
  bundle_equiv.mk'
    (equiv.trans (prod_equiv_right (domain_equiv_graph f) fiber)
                 (graph_equiv_pullback_of_trivial fiber f))
    rfl
    begin ext ⟨⟨b', b, v⟩, h⟩, refl, end

-- Pullback of a *trivialization* along any map. 🎉
def trivialization.pullback' {B B' : Type} (E : bundle B) (fiber : Type)
  (f : B' → B) (triv : trivialization E fiber) :
  trivialization (f ** E) fiber :=
  bundle_equiv.trans
    (trivialization_of_pullback_of_trivial fiber f) (f ↖≃ triv)
-/

-- Pullback of a *trivialization* along any map. 🎉
def trivialization.pullback {B B' : Type} (E : bundle B) (fiber : Type)
  (f : B' → B) (triv : trivialization E fiber) :
  trivialization (f ** E) fiber :=
    trivial_equiv_pullback_from_pt B' fiber
    ≃∘≃ (pullback_comp f (topology.map_to_point B) (topology.point ×× fiber)).symm
    ≃∘≃ (f ↖≃ (triv.symm ≃∘≃ trivial_equiv_pullback_from_pt B fiber)).symm

-- This says:
--       B' ×× fiber
--   ≃≃ (B' → point) ** (point ×× fiber)
--   ≃≃ (B' → B) ** ((B → point) ** (point ×× fiber))
--   ≃≃ f ** (B ×× fiber)
--   ≃≃ f ** E
-- As desired.

def trivialization.subset {B : Type} (U : set B) (E : bundle B) (fiber : Type)
  (triv : trivialization E fiber) :
  trivialization ((coe : U → B) ** E) fiber :=
  trivialization.pullback E fiber coe triv

-- Given a trivialization over A ⊆ B, obtain a trivialization over A ∩ V.
-- (By pulling back along A ∩ V → A.)
def trivialization.subset_of_subset {B fiber : Type} (E : bundle B) (A V : set B)
  (triv : trivialization ((coe : A → B) ** E) fiber) :
  trivialization ((coe : (A ∩ V) → B) ** E) fiber :=
  let c1 : (A ∩ V) → A := set.inclusion (set.inter_subset_left _ _) in
  bundle_equiv.trans
    (@trivialization.pullback _ _ _ fiber c1 triv)
    (pullback_comp c1 (coe : A → B) E)


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

example {J : Type} (V : open_cover J B) (h : cts E.π)
  (loc_triv : local_trivialization E fiber U h) :
  @local_trivialization B E fiber _ _ _ (I × J) (open_cover.refine U V) h :=
  { triv      := λ ij, trivialization.subset_of_subset E (U ij.1) (V ij.2) 
                          (loc_triv.triv ij.1),
    htriv     := begin rintro ⟨i, j⟩, 
      unfold trivialization.subset_of_subset,
      sorry, -- make continuity lemmas for ≃≃s
     end,
    htriv_inv := sorry,
  }

end locally_trivial_fiber_bundle

end fiber_bundle