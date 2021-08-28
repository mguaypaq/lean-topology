import tactic
import .topology
noncomputable theory

section covers

-- cover of a set
structure cover (I X : Type) :=
  (part : I → set X)
  (hx : ∀ (x : X), ∃ (i : I), x ∈ part i)

-- consistent functions on each part of the cover
structure gluing_data (I X Y : Type) :=
  (U : cover I X)
  (f : Π (i : I), (U.part i) → Y)
  (hglue : ∀ (i j : I) (x : X) (hxi : x ∈ U.part i) (hxj : x ∈ U.part j),
    (f i) ⟨x, hxi⟩ = (f j) ⟨x, hxj⟩)

-- what it means for f : X → Y to be compatible with gluing data
def compatible {I X Y : Type} (gldata : gluing_data I X Y) (f : X → Y) :=
  ∀ (i : I) (x : X) (hxi : x ∈ gldata.U.part i), f x = gldata.f i ⟨x, hxi⟩

lemma compatible_iff_restrict_eq
  {I X Y : Type} (gldata : gluing_data I X Y) {f : X → Y} :
  compatible gldata f ↔ ∀ (i : I), subtype.restrict f _ = gldata.f i :=
begin
  split; intros hf i, specialize hf i,
  ext ⟨x, hx⟩, rw subtype.restrict_apply, exact hf x hx,
  intros x hx, rw ← hf, rw subtype.restrict_apply,
end

-- existence of compatible function
-- (uses choice, even though the result is unique)
def mk_function {I X Y : Type} (gldata : gluing_data I X Y) : X → Y :=
λ x, let ⟨i, hxi⟩ := classical.subtype_of_exists (gldata.U.hx x) in
  gldata.f i ⟨x, hxi⟩

lemma mk_compatible {I X Y} (gldata : @gluing_data I X Y) :
  compatible gldata (mk_function gldata) :=
begin
  intros i x hxi,
  let j := classical.subtype_of_exists (gldata.U.hx x),
  exact gldata.hglue j.val i x j.prop hxi,
end

lemma compatible_unique {I X Y : Type} (gldata : @gluing_data I X Y) (f g : X → Y) :
  compatible gldata f → compatible gldata g → f = g :=
begin
  intros hf hg,
  ext, obtain ⟨i, hxi⟩ := gldata.U.hx x,
  specialize hf i x hxi,
  specialize hg i x hxi,
  rwa [hf, hg],
end

section refine

variables
  (I J X Y : Type)
  (CI : cover I X)
  (CJ : cover J X)
  (gldata : gluing_data I X Y)

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
    refine I J X gldata.U CJ, -- U
    λ ⟨i, j⟩ ⟨x, hxij⟩,
    gldata.f i ⟨x, hxij.left⟩,
    λ ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ x ⟨hxi₁, hxj₁⟩ ⟨hxi₂, hxj₂⟩,
    gldata.hglue i₁ i₂ x hxi₁ hxi₂,
  ⟩

variable (f : X → Y)

lemma compat_of_refine_of_compat :
  compatible gldata f →
  compatible (gl_refine _ _ _ _ CJ gldata) f :=
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
  (f : Π (i : I), (U.part i) → Y)
  (hglue : ∀ (i j : I) (x : X) (hxi : x ∈ U.part i) (hxj : x ∈ U.part j),
    (f i) ⟨x, hxi⟩ = (f j) ⟨x, hxj⟩)
  (hf : Π (i : I), @cts _ _ (topology.subspace_topology TX (U.part i)) TY (f i))

instance : has_coe (cts_gluing_data I X Y TX TY) (gluing_data I X Y) :=
  ⟨λ gldata, ⟨gldata.U, gldata.f, gldata.hglue⟩⟩

variables
  (U : open_cover I X TX) (gldata : cts_gluing_data I X Y TX TY)
  (f g : X → Y)

lemma cts_iff_cts_on_cover (f : X → Y) : cts TX TY f ↔ 
  Π (i : I), @cts _ _ (topology.subspace_topology TX (U.part i)) TY
                      (subtype.restrict f _) :=
begin
  split,
  intros hf i, apply pullback_cts_along_inverse_image, exact hf,
  intro hfi,
  -- check continuity pointwise, then on a piece of the cover
  rw cts_iff_ptwise_cts, intro x,
  obtain ⟨i, hxi⟩ := U.hx x, specialize hfi i,
  rw cts_iff_ptwise_cts at hfi, specialize hfi ⟨x, hxi⟩,
  rwa cts_at_pt_of_open TX TY f (U.part i) (U.hopen i) x hxi,
end

-- function compatible with cts gluing data is cts
-- (mostly equivalent to cts_iff_cts_on_cover)
lemma cts_of_cts_compat :
  compatible (gldata : gluing_data I X Y) f → cts TX TY f :=
begin
  intro hf,
  rw cts_iff_cts_on_cover I X Y TX TY gldata.U,
  rw compatible_iff_restrict_eq at hf,
  intro i, specialize hf i, convert gldata.hf i,
end

-- the glued function is continuous! 🎉
lemma mk_function_cts : cts TX TY (mk_function (gldata : gluing_data I X Y)) :=
  @cts_of_cts_compat I X Y TX TY gldata
  (mk_function (gldata : gluing_data I X Y))
  (mk_compatible ↑gldata)

section fiber_bundle

parameters 

end fiber_bundle

end open_cover
