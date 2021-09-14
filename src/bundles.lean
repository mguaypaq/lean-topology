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

end trivial_bundle

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
def trivialization.pullback {B B' : Type} {E : bundle B} {fiber : Type}
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

def trivialization.subset {B : Type} (U : set B) {E : bundle B} {fiber : Type}
  (triv : trivialization E fiber) :
  trivialization ((coe : U → B) ** E) fiber :=
  trivialization.pullback coe triv

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

section cts_bundle


-- Bundle maps

variables {B : Type} --[topology B]

lemma bundle_map.id.cts  (E : bundle B) [topology E.space] : cts (bundle_map.id E) := cts.id

variables {E F G : bundle B} [topology E.space] [topology F.space] [topology G.space] 

lemma bundle_map.comp.cts {φ' : F →→ G} {φ : E →→ F} (hφ' : cts φ'.map) (hφ : cts φ.map) :
  cts (φ' ∘∘ φ).map := cts_of_comp _ _ hφ hφ'

-- Bundle equivalences

lemma bundle_equiv.symm.cts {φ : E ≃≃ F} (hφ_inv : cts φ.inv_bundle_map) :
  cts φ.symm.to_bundle_map := hφ_inv
lemma bundle_equiv.symm.inv_cts {φ : E ≃≃ F} (hφ : cts φ.to_bundle_map) :
  cts φ.symm.inv_bundle_map := hφ

lemma bundle_equiv.trans.cts {φ : E ≃≃ F} {φ' : F ≃≃ G}
  (hφ'_cts : cts φ'.to_bundle_map) (hφ_cts : cts φ.to_bundle_map):
  cts (bundle_equiv.trans φ φ').to_bundle_map.map := bundle_map.comp.cts hφ'_cts hφ_cts
lemma bundle_equiv.trans.inv_cts {φ : E ≃≃ F} {φ' : F ≃≃ G}
  (hφ'_inv_cts : cts φ'.inv_bundle_map) (hφ_inv_cts : cts φ.inv_bundle_map):
  cts (bundle_equiv.trans φ φ').inv_bundle_map.map := bundle_map.comp.cts hφ_inv_cts hφ'_inv_cts

lemma bundle_equiv.mk'.cts {φ : E.space ≃ F.space}
  {hφ : F.π ∘ φ.to_fun = E.π} {hφ_inv : E.π ∘ φ.inv_fun = F.π} (hφ_cts : cts φ) :
  cts (bundle_equiv.mk' φ hφ hφ_inv).to_bundle_map := hφ_cts
lemma bundle_equiv.mk'.inv_cts {φ : E.space ≃ F.space}
  {hφ : F.π ∘ φ.to_fun = E.π} {hφ_inv : E.π ∘ φ.inv_fun = F.π} (hφ_inv_cts : cts φ.inv_fun) :
  cts (bundle_equiv.mk' φ hφ hφ_inv).inv_bundle_map := hφ_inv_cts

-- Pullback maps and equivs

variables {B' : Type} (f : B' → B) [topology B] [topology B'] --(hf : cts f)

lemma pullback_map.cts {φ : E →→ F} (hφ : cts φ.map) :
  cts (f ↖* φ).map :=
begin
  apply fiber_product.exact.map.cts,
  exact fiber_product.fst.cts _ _,
  apply cts_of_comp _ φ.map _ hφ,
  exact fiber_product.snd.cts _ _,
end

lemma pullback_bundle_equiv.cts {φ : E ≃≃ F} (hφ_cts : cts φ.to_bundle_map) :
  cts (f ↖≃ φ).to_bundle_map := pullback_map.cts f hφ_cts

lemma pullback_bundle_equiv.inv_cts {φ : E ≃≃ F} (hφ_inv_cts : cts φ.inv_bundle_map) :
  cts (f ↖≃ φ).inv_bundle_map := pullback_map.cts f hφ_inv_cts

variables {B'' : Type} [topology B''] (g : B'' → B')

lemma pullback_comp.cts (hf : cts f) : cts (pullback_comp g f E).to_bundle_map := 
  bundle_equiv.mk'.cts (fiber_product.comp_base.cts _ _ _ hf)

lemma pullback_comp.inv_cts (hg : cts g) : cts (pullback_comp g f E).inv_bundle_map :=
  bundle_equiv.mk'.inv_cts (fiber_product.comp_base.inv_cts _ _ _ hg)


-- Trivializations

variables (fiber : Type) [topology fiber]

lemma trivial_equiv_pullback_from_pt.cts :
  cts (trivial_equiv_pullback_from_pt B fiber).to_bundle_map :=
begin
  apply bundle_equiv.mk'.cts _,
  apply restrict_cod_cts _,
  apply prod_equiv_left.cts,
  exact prod_point_left.inv_cts fiber,
  exact prod_point_left.cts fiber,
end

lemma trivial_equiv_pullback_from_pt.inv_cts :
  cts (trivial_equiv_pullback_from_pt B fiber).inv_bundle_map :=
begin
  apply bundle_equiv.mk'.inv_cts _,
  apply cts_of_comp _ _ coe_cts,
  apply prod_equiv_left.cts,
  exact prod_point_left.cts fiber,
  exact prod_point_left.inv_cts fiber,
end

lemma trivialization.pullback.cts (hf : cts f) {triv : trivialization E fiber}
  (htriv_cts : cts triv.to_bundle_map) :
  cts (trivialization.pullback f triv).to_bundle_map :=
begin
  apply bundle_equiv.trans.cts _ _, by apply_instance,
    apply bundle_equiv.symm.cts,
    apply pullback_map.cts,
    apply bundle_equiv.trans.inv_cts _ _, by apply_instance,
      apply trivial_equiv_pullback_from_pt.inv_cts,
      exact htriv_cts, -- assumption used!!
    apply bundle_equiv.trans.cts _ _, by apply_instance,
      apply bundle_equiv.symm.cts,
      apply pullback_comp.inv_cts, exact hf, -- assumption used!!
      apply trivial_equiv_pullback_from_pt.cts,
end

lemma trivialization.pullback.inv_cts {triv : trivialization E fiber} 
  (htriv_inv_cts : cts triv.inv_bundle_map) :
  cts (trivialization.pullback f triv).inv_bundle_map :=
begin
  apply bundle_equiv.trans.inv_cts _ _, by apply_instance,
    apply bundle_equiv.symm.inv_cts,
    apply pullback_map.cts,
    apply bundle_equiv.trans.cts _ _, by apply_instance,
      apply trivial_equiv_pullback_from_pt.cts,
      exact htriv_inv_cts, -- assumption used!!
    apply bundle_equiv.trans.inv_cts _ _, by apply_instance,
      apply bundle_equiv.symm.inv_cts,
      apply pullback_comp.cts, apply map_to_point_cts,
      apply trivial_equiv_pullback_from_pt.inv_cts,
end


/-
structure cts_bundle (B : Type) [topology B] :=
  (space : Type)
  (top : topology space)
  (π : space → B)
  (hπ : cts π)

instance cts_bundle_to_bundle (B : Type) [topology B] :
  has_coe (cts_bundle B) (bundle B) := ⟨λ E, ⟨E.space, E.π⟩⟩

attribute [instance] cts_bundle.top

variables {B : Type} [topology B] (E F : cts_bundle B)

structure cts_bundle_map :=
  (map : E.space → F.space)
  (h : F.π ∘ map = E.π)
  (map_cts : cts map)

instance cts_bundle_map_to_bundle_map : has_coe (cts_bundle_map E F) (@bundle_map B ↑E ↑F) :=
  ⟨λ φ, ⟨φ.map, φ.h⟩⟩

structure cts_bundle_equiv :=
  (map  : cts_bundle_map E F)
  (inv_map : cts_bundle_map F E)
  (left_inv : ↑inv_map ∘∘ ↑map = bundle_map.id ↑E)
  (right_inv : ↑map ∘∘ ↑inv_map = bundle_map.id ↑F) :
  
def cts_bundle_equiv.mk' {B : Type} [topology B] {E F : cts_bundle B}
  (map  : cts_bundle_map E F)
  (inv_map : cts_bundle_map F E)
  (left_inv : inv_map.to_bundle_map ∘∘ map.to_bundle_map = bundle_map.id E.to_bundle)
  (right_inv : map.to_bundle_map ∘∘ inv_map.to_bundle_map = bundle_map.id F.to_bundle) :
  cts_bundle_equiv E F :=
  { to_bundle_equiv :=
    { to_bundle_map := map.to_bundle_map,
       inv_bundle_map := inv_map.to_bundle_map,
      left_inv := left_inv,
      right_inv := right_inv },
     map_cts := map.map_cts,
     inv_cts := inv_map.map_cts}

def cts_bundle_equiv.to_cts_bundle_map {B : Type} [topology B] {E F : cts_bundle B} 
  (φ : cts_bundle_equiv E F) : cts_bundle_map E F := ⟨φ.to_bundle_map, φ.map_cts⟩

def cts_bundle_equiv.inv_cts_bundle_map {B : Type} [topology B] {E F : cts_bundle B} 
  (φ : cts_bundle_equiv E F) : cts_bundle_map F E := ⟨φ.inv_bundle_map, φ.inv_cts⟩

def cts_bundle_map.id {B : Type} [topology B] (E : cts_bundle B) : cts_bundle_map E E :=
  { map_cts := cts.id, ..(bundle_map.id E.to_bundle) }

def cts_bundle_map.comp {B : Type}

-- What is the most appropriate / efficient thing to do here?

/-

structure cts_bundle (B : Type) [topology B] extends (bundle B) :=
  (top : topology to_bundle.space)
  (hπ : cts to_bundle.π)

structure cts_bundle_map {B : Type} [topology B] {E F : cts_bundle B} extends
  (bundle_map E.to_bundle F.to_bundle) :=
  (hcts : @cts _ _ E.top F.top to_bundle_map.map)

...

But then we have to start explicitly referring to the topology everywhere.

Or: just assume [topology t] for all relevant spaces t and (hf: cts f) for
all relevant f?

Or: put back in an assumption (hf : adjective f) throughout, where the adjective is part
of the data of the bundle.


-/
-/

end cts_bundle

end fiber_bundle