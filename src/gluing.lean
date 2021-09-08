import tactic
import .topology
noncomputable theory

section cover

-- cover of a set
structure cover (I X : Type) :=
  (part : I → set X)
  (hx : ∀ (x : X), ∃ (i : I), x ∈ part i)

-- coercion so we can write "U i" when (U : cover I X) and (i : I)
instance cover_to_parts (I X : Type) : has_coe_to_fun (cover I X) :=
  {F   := λ _, I → set X,
   coe := λ U, U.part}

@[reducible]
def pullback_cover {I X Y : Type} (f : X → Y) (U : cover I Y) : cover I X :=
  ⟨ λ i, f ⁻¹' (U i),
    λ x, U.hx (f x)⟩
infix `⁻¹c`:110 := pullback_cover

lemma pullback_cover.comp {I X Y Z : Type} (f : X → Y) (g : Y → Z)
  (U : cover I Z) : (g ∘ f) ⁻¹c U = f ⁻¹c (g ⁻¹c U) := by split

lemma cover_set_eq {I X : Type} (U : cover I X) (A : set X) :
  A = ⋃₀ {A' | ∃ j, A' = (U j) ∩ A} :=
begin
  ext a, split; intro ha,
  obtain ⟨i, hi⟩ := U.hx a,
  use (U i) ∩ A, exact ⟨⟨i, rfl⟩, hi, ha⟩,
  obtain ⟨A', ⟨j, hj⟩, hA''⟩ := ha, rw hj at hA'', exact hA''.2,
end

example {X Y : Type} (f : X → Y) (U : set Y) : set.preimage f U → U :=
  λ x, ⟨f x.val, x.prop⟩

example {X Y : Type} (f : X → Y) : X → f '' set.univ :=
  λ x, ⟨f x, ⟨x, trivial, rfl⟩⟩


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

lemma compat_of_refine_of_compat (f : X → Y) :
  compatible gl f →
  compatible (gl_refine _ _ _ _ CJ gl) f :=
begin
  rintros hf ⟨i, j⟩ x ⟨hxi, hxj⟩,
  exact hf i x hxi,
end

end refine

end cover

section open_cover
open topology
--(@pullback J E' B π' V)

structure open_cover (I X : Type) [topology X] extends (cover I X) :=
  (hopen : ∀ (i : I), part i ∈ opens X)

instance (I X : Type) [topology X] :
  has_coe (open_cover I X) (cover I X) := ⟨λ U, ⟨U.part, U.hx⟩⟩

structure cts_gluing_data (I X Y : Type) [topology X] [topology Y] :=
  (U : open_cover I X)
  (f : Π (i : I), (U i) → Y)
  (hglue : ∀ (i j : I) (x : X) (hxi : x ∈ U i) (hxj : x ∈ U j),
    (f i) ⟨x, hxi⟩ = (f j) ⟨x, hxj⟩)
  (hf : Π (i : I), cts (f i))

instance (I X Y : Type) [topology X] [topology Y] :
  has_coe (cts_gluing_data I X Y) (gluing_data I X Y) :=
  ⟨λ gl, ⟨gl.U, gl.f, gl.hglue⟩⟩

variables {I X : Type} [topology X]

lemma subset_open_iff_open_cover (U : open_cover I X) (A : set X) :
  A ∈ opens X ↔ ∀ (i : I), (U i) ∩ A ∈ opens X :=
begin
  split, intros hA i, apply inter₂ _ _ (U.hopen i) hA,
  intro hA,
  rw cover_set_eq U.to_cover A,
  apply union, rintros A' ⟨i, hi⟩, rw hi, exact hA i,
end

variables {Y : Type} [topology Y]
  (U : open_cover I X) (gl : cts_gluing_data I X Y)
  (f g : X → Y)

@[reducible]
def pullback_open_cover (hf : cts f) (U : open_cover I Y) : open_cover I X :=
  ⟨ pullback_cover f ↑U,
    λ i, hf _ (U.hopen i)⟩

lemma cts_iff_cts_on_cover (f : X → Y) : cts f ↔ 
  Π (i : I), @cts _ _ (subspace_topology (U i)) _
                      (subtype.restrict f (U i)) :=
begin
  split,
  intros hf i, apply pullback_cts_along_inverse_image, exact hf,
  intro hfi,
  -- check continuity pointwise, then on a piece of the cover
  rw cts_iff_ptwise_cts, intro x,
  obtain ⟨i, hxi⟩ := U.hx x, specialize hfi i,
  rw cts_iff_ptwise_cts at hfi, specialize hfi ⟨x, hxi⟩,
  rwa cts_at_pt_of_open f (U i) (U.hopen i) x hxi,
end

-- function compatible with cts gluing data is cts
-- (mostly equivalent to cts_iff_cts_on_cover)
lemma cts_of_cts_compat :
  compatible (gl : gluing_data I X Y) f → cts f :=
begin
  intro hf,
  rw cts_iff_cts_on_cover gl.U,
  rw compatible_iff_restrict_eq at hf,
  intro i, specialize hf i, convert gl.hf i,
end

-- the glued function is continuous! 🎉
lemma mk_function_cts : cts (mk_function (gl : gluing_data I X Y)) :=
  cts_of_cts_compat gl
  (mk_function (gl : gluing_data I X Y))
  (mk_compatible ↑gl)

end open_cover

-- an attempt at doing covers using maps rather than subsets
section b_cover

structure b_cover (I X : Type) :=
  (part   : I → Type)
  (map    : Π {i : I}, (part i) → X)
  (hx     : ∀ (x : X), ∃ i (u : part i), map u = x)

instance b_cover_to_parts (I X : Type) : has_coe_to_fun (b_cover I X) :=
  {F   := λ _, I → Type,
   coe := λ U, U.part}

def to_fun {I X : Type} (U : b_cover I X) (i : I) : U i → X :=
  λ x, U.map x

structure b_cover₂ (I X : Type) extends (b_cover I X) :=
  (part₂   : I → I → Type)
  (map₂l   : Π {i j : I}, (part₂ i j) → part i)
  (map₂r   : Π {i j : I}, (part₂ i j) → part j)
  (compat₂ : Π {i j : I} (u_ij : part₂ i j), 
             map (map₂l u_ij) = map (map₂r u_ij))
  (hx₂     : ∀ {i j : I} {u_i : part i} {u_j : part j},
             map u_i = map u_j ↔
             ∃ u_ij, map₂l u_ij = u_i ∧ map₂r u_ij = u_j)

-- consistent functions on each part of the cover
structure b_gluing_data (I X Y : Type) extends (b_cover₂ I X) :=
  (f  : Π {i : I}, part i → Y)
  (hglue : ∀ {i j : I} (u : part₂ i j),
           f (map₂l u) = f (map₂r u))

-- what it means for f : X → Y to be compatible with gluing data
def b_compatible {I X Y : Type} (gl : b_gluing_data I X Y) (f : X → Y) :=
  ∀ {i : I} (u : gl.part i), f (gl.map u) = gl.f u

-- existence of compatible function
-- (uses choice, even though the result is unique)
def b_mk_function {I X Y : Type} (gl : b_gluing_data I X Y) : X → Y :=
  λ x, let hi := classical.some_spec (gl.hx x) in
       let u := classical.some hi in
       gl.f u

lemma b_mk_compatible {I X Y} (gl : b_gluing_data I X Y) :
  b_compatible gl (b_mk_function gl) :=
begin
  intros i v,
  let hi := classical.some_spec (gl.hx (gl.map v)),
  let u := classical.some hi,
  let hu := classical.some_spec hi, rw gl.hx₂ at hu,
  change gl.f u = gl.f v,
  obtain ⟨uij, hl, hr⟩ := hu, change gl.map₂l uij = u at hl,
  have key := gl.hglue uij, rwa [hl, hr] at key,
end

lemma b_compatible_unique {I X Y : Type} (gl : b_gluing_data I X Y) (f g : X → Y) :
  b_compatible gl f → b_compatible gl g → f = g :=
begin
  intros hf hg,
  ext, obtain ⟨i, ⟨u, hu⟩⟩ := gl.hx x,
  specialize hf u, specialize hg u, rw hu at *,
  rwa [hf, hg],
end

section b_refine

variables
  (I J X Y : Type)
  (CI : b_cover I X)
  (CJ : b_cover J X)
  (gl : b_gluing_data I X Y)

def b_refine : b_cover (I × J) X :=
 ⟨λ ⟨i, j⟩, {uv : CI i × CJ j // CI.map uv.fst = CJ.map uv.snd},
  λ ⟨i, j⟩ ⟨uv, h⟩, CI.map uv.fst,
  begin
    intro x,
    obtain ⟨i, ⟨u, hu⟩⟩ := CI.hx x,
    obtain ⟨j, ⟨v, hv⟩⟩ := CJ.hx x,
    use ⟨i, j⟩, use ⟨u, v⟩, rwa [hu, hv],
  end⟩

/- 
Note: this is asymmetric: f is defined on Uᵢ ∩ Vⱼ 
as the restriction of f from Uᵢ, not Vⱼ.
-/
def b_gl_refine : b_gluing_data (I × J) X Y := sorry
/-
  ⟨ -- U, f, hglue
    b_refine I J X CI CJ, -- U
    λ ⟨i, j⟩ ⟨x, hxij⟩,
    gl.f i ⟨x, hxij.left⟩,
    λ ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ x ⟨hxi₁, hxj₁⟩ ⟨hxi₂, hxj₂⟩,
    gl.hglue i₁ i₂ x hxi₁ hxi₂,
  ⟩
-/

end b_refine
end b_cover