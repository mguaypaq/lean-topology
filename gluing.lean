import tactic
import .topology
noncomputable theory

section covers

-- cover of a set
structure cover (I X : Type) :=
  (part : I → set X)
  (hx : ∀ (x : X), ∃ (i : I), x ∈ part i)

-- coercion so we can write "U i" when (U : cover I X) and (i : I)
instance cover_to_parts (I X : Type) : has_coe_to_fun (cover I X) :=
  {F   := λ _, I → set X,
   coe := λ U, U.part}

-- consistent functions on each part of the cover
structure gluing_data (I X Y : Type) :=
  (U : cover I X)
  (f : Π (i : I), U i → Y)
  (hglue : ∀ (i j : I) (x : X) (hxi : x ∈ U i) (hxj : x ∈ U j),
    (f i) ⟨x, hxi⟩ = (f j) ⟨x, hxj⟩)

-- what it means for f : X → Y to be compatible with gluing data
def compatible {I X Y : Type} (gl : gluing_data I X Y) (f : X → Y) :=
  ∀ (i : I) (x : X) (hxi : x ∈ gl.U i), f x = gl.f i ⟨x, hxi⟩

lemma compatible_iff_restrict_eq
  {I X Y : Type} (gl : gluing_data I X Y) {f : X → Y} :
  compatible gl f ↔ ∀ (i : I), subtype.restrict f _ = gl.f i :=
begin
  split; intros hf i, specialize hf i,
  ext ⟨x, hx⟩, rw subtype.restrict_apply, exact hf x hx,
  intros x hx, rw ← hf, rw subtype.restrict_apply,
end

-- existence of compatible function
-- (uses choice, even though the result is unique)
def mk_function {I X Y : Type} (gl : gluing_data I X Y) : X → Y :=
λ x, let ⟨i, hxi⟩ := classical.subtype_of_exists (gl.U.hx x) in
  gl.f i ⟨x, hxi⟩

lemma mk_compatible {I X Y} (gl : @gluing_data I X Y) :
  compatible gl (mk_function gl) :=
begin
  intros i x hxi,
  let j := classical.subtype_of_exists (gl.U.hx x),
  exact gl.hglue j.val i x j.prop hxi,
end

lemma compatible_unique {I X Y : Type} (gl : @gluing_data I X Y) (f g : X → Y) :
  compatible gl f → compatible gl g → f = g :=
begin
  intros hf hg,
  ext, obtain ⟨i, hxi⟩ := gl.U.hx x,
  specialize hf i x hxi,
  specialize hg i x hxi,
  rwa [hf, hg],
end

section refine

variables
  (I J X Y : Type)
  (CI : cover I X)
  (CJ : cover J X)
  (gl : gluing_data I X Y)

def refine : cover (I × J) X :=
 ⟨λ ⟨i, j⟩, (CI.part i) ∩ (CJ.part j),
  λ x, let ⟨i, hxi⟩ := CI.hx x in
       let ⟨j, hxj⟩ := CJ.hx x in
       ⟨⟨i, j⟩, ⟨hxi, hxj⟩⟩⟩

/- 
Note: this is asymmetric: f is defined on Uᵢ ∩ Vⱼ 
as the restriction of f from Uᵢ, not Vⱼ.
-/
def gl_refine : gluing_data (I × J) X Y :=
  ⟨ -- U, f, hglue
    refine I J X gl.U CJ, -- U
    λ ⟨i, j⟩ ⟨x, hxij⟩,
    gl.f i ⟨x, hxij.left⟩,
    λ ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ x ⟨hxi₁, hxj₁⟩ ⟨hxi₂, hxj₂⟩,
    gl.hglue i₁ i₂ x hxi₁ hxi₂,
  ⟩

variable (f : X → Y)

lemma compat_of_refine_of_compat :
  compatible gl f →
  compatible (gl_refine _ _ _ _ CJ gl) f :=
begin
  rintros hf ⟨i, j⟩ x ⟨hxi, hxj⟩,
  exact hf i x hxi,
end

end refine

end covers

section open_cover

open topology

variables (I X Y : Type) (TX : topology X) (TY : topology Y)

structure open_cover extends (cover I X) :=
  (hopen : ∀ (i : I), part i ∈ TX.opens)

instance : has_coe (open_cover I X TX) (cover I X) := ⟨λ U, ⟨U.part, U.hx⟩⟩

structure cts_gluing_data :=
  (U : open_cover I X TX)
  (f : Π (i : I), (U i) → Y)
  (hglue : ∀ (i j : I) (x : X) (hxi : x ∈ U i) (hxj : x ∈ U j),
    (f i) ⟨x, hxi⟩ = (f j) ⟨x, hxj⟩)
  (hf : Π (i : I), @cts _ _ (topology.subspace_topology TX (U i)) TY (f i))

instance : has_coe (cts_gluing_data I X Y TX TY) (gluing_data I X Y) :=
  ⟨λ gl, ⟨gl.U, gl.f, gl.hglue⟩⟩

variables
  (U : open_cover I X TX) (gl : cts_gluing_data I X Y TX TY)
  (f g : X → Y)

lemma cts_iff_cts_on_cover (f : X → Y) : cts TX TY f ↔ 
  Π (i : I), @cts _ _ (topology.subspace_topology TX (U i)) TY
                      (subtype.restrict f _) :=
begin
  split,
  intros hf i, apply pullback_cts_along_inverse_image, exact hf,
  intro hfi,
  -- check continuity pointwise, then on a piece of the cover
  rw cts_iff_ptwise_cts, intro x,
  obtain ⟨i, hxi⟩ := U.hx x, specialize hfi i,
  rw cts_iff_ptwise_cts at hfi, specialize hfi ⟨x, hxi⟩,
  rwa cts_at_pt_of_open TX TY f (U i) (U.hopen i) x hxi,
end

-- function compatible with cts gluing data is cts
-- (mostly equivalent to cts_iff_cts_on_cover)
lemma cts_of_cts_compat :
  compatible (gl : gluing_data I X Y) f → cts TX TY f :=
begin
  intro hf,
  rw cts_iff_cts_on_cover I X Y TX TY gl.U,
  rw compatible_iff_restrict_eq at hf,
  intro i, specialize hf i, convert gl.hf i,
end

-- the glued function is continuous! 🎉
lemma mk_function_cts : cts TX TY (mk_function (gl : gluing_data I X Y)) :=
  @cts_of_cts_compat I X Y TX TY gl
  (mk_function (gl : gluing_data I X Y))
  (mk_compatible ↑gl)

section fiber_bundle

def res_l {X Y : Type} {A B : set X} (g : A → Y) : A ∩ B → Y :=
  λ ⟨a, hab⟩, g ⟨a, hab.1⟩

def res_r {X Y : Type} {A B : set X} (g : B → Y) : A ∩ B → Y :=
  λ ⟨a, hab⟩, g ⟨a, hab.2⟩

-- collecting the data of a potential bundle
-- (this definition does not assert any actual properties of π)
structure prebundle :=
  (base fiber total_space : Type)
  (TB : topology base)
  (TF : topology fiber)
  (TT : topology total_space)
  (π : total_space → base)
  (hπ : function.surjective π ∧ cts TT TB π)

-- what it means for trivialize over a subset
structure trivialize_subset (E : prebundle) (U : set E.base) :=
  (φ : U × E.fiber → E.π ⁻¹' U)
  (hφ_homeo : homeo ↑((E.TB : topology U), E.TF) ↑E.TT φ)
  (hφ_proj : ∀ u v, E.π (φ ⟨u, v⟩) = u)

-- a fiber bundle together with a choice of trivialization datum
structure structured_fiber_bundle extends prebundle :=
  (I : Type)
  (U : open_cover I base TB)
  (triv (i : I) : trivialize_subset (to_prebundle) (U i))

-- incomplete, but will likely be needed
def refine_trivializing
  (E : prebundle) (U : set E.base) (triv : trivialize_subset E U)
  (U' : set E.base) (hU' : U' ⊆ U) :
  trivialize_subset E U' := sorry


/- from earlier attempt to define fiber bundle, including transition functions
  (trans (i j : I) : (U i) ∩ (U j) → fiber → fiber)
  (htrans (i j : I) :
    (∀ (u : (U i) ∩ (U j)) (v : fiber),
      let t := (triv i ⟨⟨u, u.2.1⟩, v⟩) in -- ⟨t.val, h : t ∈ π ⁻¹' U i⟩
      triv_inv j ⟨t.val, begin simp, rw (htriv i).2.2.2 ⟨u, u.2.1⟩ v, exact u.2.2, end⟩
        = ⟨⟨u, u.2.2⟩, trans i j u v⟩))
-/


-- This was hard to write -- describing the transition functions especially.
-- It's annoying to have to coerce between different sets.
-- I'm not even sure it's complete.
-- Eventually it will need the transition function to be a rescaling.


end fiber_bundle

end open_cover
