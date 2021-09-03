import tactic
import .topology
import .gluing

section fiber_space

variables {E E' B : Type} {π : E → B} {π' : E' → B} {φ : E → E'}

lemma fiber_map_subset (hφ : π' ∘ φ = π) {U : set B} {e : E} :
  e ∈ π ⁻¹' U ↔ φ e ∈ π' ⁻¹' U := by {simp, rw [← function.comp_app π' φ, hφ]}


lemma fiber_map_subset' (hφ : π' ∘ φ = π) {U : set B} {e : E} :
  π e ∈ U ↔ π' (φ e) ∈ U := by rw [← function.comp_app π' φ, hφ]


@[simp]
def res_subset (hφ : π' ∘ φ = π) (U : set B) :
  π ⁻¹' U → π' ⁻¹' U :=
  λ ⟨e, he⟩, ⟨φ e, (fiber_map_subset hφ).mp he⟩

lemma fiber_map_inj_iff_res_inj (hφ : π' ∘ φ = π) :
  function.injective φ ↔ 
  ∀ (U : set B), function.injective (res_subset hφ U) :=
begin
  split,
    intros h U,
    rintros ⟨e1, he1⟩ ⟨e2, he2⟩, simp, apply h,
  intro h, specialize h set.univ,
    rintros e1 e2 he, unfold function.injective at h, simp at h,
    apply h, exact he,
end

lemma fiber_map_surj_iff_res_surj (hφ : π' ∘ φ = π) :
  function.surjective φ ↔ 
  ∀ (U : set B), function.surjective (res_subset hφ U) :=
begin
  split,
    rintros h U ⟨e', he'⟩,
    obtain ⟨e, he⟩ := h e',
    simp, exact ⟨e, by rwa [fiber_map_subset' hφ, he], he⟩,
  intro h, specialize h set.univ,
  unfold function.surjective at h, simp at h, apply h,
end

lemma fiber_map_bij_iff_res_bij (hφ : π' ∘ φ = π) :
  function.bijective φ ↔ 
  ∀ (U : set B), function.bijective (res_subset hφ U) :=
begin
  unfold function.bijective,
  rw forall_and_distrib,
  rw ← fiber_map_inj_iff_res_inj,
  rw ← fiber_map_surj_iff_res_surj,
end

section fiber_bundle

open topology

variables [topology B] [topology E] [topology E']

lemma fiber_map_cts_iff_res_cts
  (hπ_cts : cts π) (hπ'_cts : cts π') (hφ : π' ∘ φ = π) :
  topology.cts φ ↔
  ∀ U (hU : U ∈ topology.opens B), cts (res_subset hφ U) :=
begin
  split,
  -- mp
  intros hφ_cts U hU V hV,
  let V_E' := from_sub _ V,
  have hV_E' := (from_sub_open_iff _ (hπ'_cts U hU) V).mp hV,
  specialize hφ_cts V_E' hV_E',
  have : res_subset hφ U ⁻¹' V = to_sub _ (φ ⁻¹' V_E'),
    ext ⟨e, he⟩, simp,
    have he2 := (fiber_map_subset hφ).mp he,
    split, intro h, exact ⟨⟨φ e, he2⟩, h, rfl⟩,
    rintro ⟨⟨e', he'⟩, he'', he'''⟩, convert he'', rw ← he''', simp,
  rw [this, to_sub_open_iff],
  use (φ ⁻¹' V_E'), exact ⟨hφ_cts, rfl⟩,
  -- mpr
  intros hφU_cts V hV,
  specialize hφU_cts set.univ topology.univ_open (to_sub set.univ V),
  rw to_sub_open_iff (π' ⁻¹' set.univ) (to_sub set.univ V) at hφU_cts,
  specialize hφU_cts ⟨V, hV, rfl⟩,
  rw from_sub_open_iff at hφU_cts,
  suffices : from_sub (π ⁻¹' set.univ) (res_subset hφ set.univ ⁻¹' to_sub set.univ V) = φ ⁻¹' V, rwa ← this,
  ext e, simp, exact topology.univ_open,
end

lemma fiber_map_open_iff_res_open
  (hπ_cts : cts π) (hπ'_cts : cts π') (hφ : π' ∘ φ = π) :
  (∀ V ∈ topology.opens E, φ '' V ∈ topology.opens E') ↔
  ∀ U (hU : U ∈ topology.opens B) V (hV : V ∈ topology.opens (π ⁻¹' U)),
  ((res_subset hφ U) '' V) ∈ topology.opens (π' ⁻¹' U) :=
begin
  split,
  -- mp
  intros hφ_open U hU V hV,
  let V_E := from_sub _ V,
  have hV_E := (from_sub_open_iff _ (hπ_cts U hU) V).mp hV,
  specialize hφ_open V_E hV_E,
  have : res_subset hφ U '' V = to_sub _ (φ '' V_E),
    ext ⟨e', he'⟩, simp,
    split,
    rintro ⟨e, ⟨he1, he2⟩, he3⟩, use e, split, use e, exact he1, exact ⟨he2, rfl⟩, exact he3,
    rintro ⟨e, ⟨⟨e2, he2⟩, he2'⟩, he3⟩, rw ← he3 at he', rw ← fiber_map_subset hφ at he',
    use e, split, use he', convert he2'.1, rw ← he2'.2, refl, exact he3,
  rw [this, to_sub_open_iff],
  use (φ '' V_E), exact ⟨hφ_open, rfl⟩,
  -- mpr
  intro hφU_open, 
  specialize hφU_open set.univ topology.univ_open,
  intros V hV,
  specialize hφU_open (to_sub set.univ V),
  rw to_sub_open_iff (π ⁻¹' set.univ) (to_sub set.univ V) at hφU_open,
  specialize hφU_open ⟨V, hV, rfl⟩,
  rw from_sub_open_iff at hφU_open,
  suffices : φ '' V = from_sub (π' ⁻¹' set.univ) (res_subset hφ set.univ '' to_sub set.univ V), rwa this,
  ext e, simp, simp, exact topology.univ_open,
end

lemma fiber_map_homeo_iff_res_homeo
  (hπ_cts : cts π) (hπ'_cts : cts π') (hφ : π' ∘ φ = π) :
  homeo φ ↔
  ∀ U (hU : U ∈ topology.opens B), homeo (res_subset hφ U) :=
begin
  rw homeo_iff, conv in (homeo _) {rw homeo_iff},
  split, intros h U hU,
  exact ⟨(fiber_map_cts_iff_res_cts hπ_cts hπ'_cts hφ).mp h.1 U hU,
         (fiber_map_bij_iff_res_bij hφ).mp h.2.1 U,
         (fiber_map_open_iff_res_open hπ_cts hπ'_cts hφ).mp h.2.2 U hU⟩,
  intro h, rw [ball_and_distrib, ball_and_distrib] at h,
  obtain ⟨h1, h2, h3⟩ := h,
  rw ← fiber_map_cts_iff_res_cts hπ_cts hπ'_cts hφ at h1,
  specialize h2 set.univ topology.univ_open,
  rw ← fiber_map_open_iff_res_open hπ_cts hπ'_cts hφ at h3,
  split, exact h1,
  split, {unfold function.bijective at *,
          unfold function.injective at *,
          unfold function.surjective at *, simp at h2, exact h2},
  exact h3,
end


structure fiber_space (B : Type) :=
  (E : Type)
  (π : E → B)
infix `∈` := λ e (X : fiber_space), e ∈ X.E

structure fiber_map {B : Type} (X X' : fiber_space B) :=
  (φ : X.E → X'.E)
  (hφ_proj : X'.π ∘ φ = X.π)

instance fiber_map_to_fun {B : Type} {X X' : fiber_space B} :
  has_coe_to_fun (fiber_map X X') :=
  { F   := λ _, X.E → X'.E,
    coe := λ m, m.φ}

end fiber_bundle

end fiber_space