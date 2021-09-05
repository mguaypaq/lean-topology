import tactic
import .topology
import .gluing

section fiber_space

variables {E E' B : Type} {π : E → B} {π' : E' → B} {φ : E → E'}

def res_base (hφ : π' ∘ φ = π) (U : set B) :
  φ ⁻¹' (π' ⁻¹' U) → π' ⁻¹' U :=
  subtype.map φ (by simp)

@[simp]
lemma res_base_def (hφ : π' ∘ φ = π) (U : set B)
  (a : E) (ha : a ∈ φ ⁻¹' (π' ⁻¹' U)) :
  res_base hφ U ⟨a, ha⟩ = ⟨φ a, ha⟩ := rfl

lemma rw_res_base (hφ : π' ∘ φ = π) (U : set B) :
  φ ⁻¹' (π' ⁻¹' U) = π ⁻¹' U := by {rw [← hφ, ← set.preimage_comp]}

lemma from_sub_res_image_of_to_sub (hφ : π' ∘ φ = π)
  (U : set B) (V : set E):
  from_sub _ ((res_base hφ U) '' (to_sub _ V)) =
    (π' ⁻¹' U) ∩ (φ '' V) :=
begin
  ext e', simp, split,
  rintro ⟨e'', he'', ⟨e, he⟩, he12⟩, rw he12 at *,
  exact ⟨he'', ⟨e, he.1, he.2.2⟩⟩,
  rintro ⟨he', e, he1, he2⟩, use e', split, exact he', use e,
  simp [he2], exact ⟨he1, he'⟩,
end

lemma from_sub_res_preimage_of_to_sub (hφ : π' ∘ φ = π)
  (U : set B) (V : set E'):
  from_sub _ ((res_base hφ U) ⁻¹' (to_sub _ V)) = 
    φ ⁻¹' ((π' ⁻¹' U) ∩ V) :=
begin
  unfold from_sub, unfold to_sub, unfold res_base,
  ext e, simp, split,
  rintro ⟨x, hx⟩, rw ← hx.2.2, exact ⟨hx.1, hx.2.1⟩,
  intro h, use e, simp, exact h,
end

lemma res_base_inj_of_inj (hφ : π' ∘ φ = π)
  (hφ_inj : function.injective φ) (U : set B) : 
  function.injective (res_base hφ U) :=
begin
  apply subtype.map_injective, exact hφ_inj,
end

lemma res_base_surj_of_surj (hφ : π' ∘ φ = π)
  (hφ_surj : function.surjective φ) (U : set B) : 
  function.surjective (res_base hφ U) :=
begin
  rintro ⟨x, hx⟩, obtain ⟨y, hy⟩ := hφ_surj x,
  use y, simp, rwa hy,
  simp, exact hy,
end

lemma res_base_bij_of_bij (hφ : π' ∘ φ = π)
  (hφ_bij : function.bijective φ) (U : set B) : 
  function.bijective (res_base hφ U) :=
begin
  split,
    apply res_base_inj_of_inj hφ hφ_bij.1,
    apply res_base_surj_of_surj hφ hφ_bij.2,
end


variables {I : Type} (U : cover I B)

lemma fiber_map_inj_iff_cover_inj (hφ : π' ∘ φ = π) :
  function.injective φ ↔
  ∀ i, function.injective (res_base hφ (U i)) :=
begin
  split,
    intros hφ_inj i, apply res_base_inj_of_inj, exact hφ_inj,
  intros hφ_inj_cover e1 e2 he,
  obtain ⟨i, hi⟩ := U.hx (π' (φ e1)),
  specialize @hφ_inj_cover i ⟨e1, hi⟩ ⟨e2, by rwa he at hi⟩,
  simp at hφ_inj_cover, exact hφ_inj_cover he,
end

lemma fiber_map_surj_iff_cover_surj (hφ : π' ∘ φ = π) :
  function.surjective φ ↔
  ∀ i, function.surjective (res_base hφ (U i)) :=
begin
  split,
    intros hφ_surj i, apply res_base_surj_of_surj, exact hφ_surj,
  intro hφ_surj_cover, intro e',
  obtain ⟨i, hi⟩ := U.hx (π' e'),
  obtain ⟨⟨a, ha⟩, ha'⟩ := hφ_surj_cover i ⟨e', hi⟩,
  use a, simp at ha', exact ha',
end

lemma fiber_map_bij_iff_cover_bij (hφ : π' ∘ φ = π) :
  function.bijective φ ↔ 
  ∀ i, function.bijective (res_base hφ (U i)) :=
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
  (hπ_cts : cts π) (hπ'_cts : cts π') (hφ_cts : cts φ)
  (hφ : π' ∘ φ = π)
  (U : set B) (hU : U ∈ opens B) :
  cts (res_base hφ U) :=
  subtype_map_cts hφ_cts

lemma fiber_map_cts_iff_cover_cts
  (hπ_cts : cts π) (hπ'_cts : cts π') (hφ : π' ∘ φ = π) :
  cts φ ↔
  ∀ j, cts (res_base hφ (V j)) :=
begin
  split,
    intros hφ_cts j,
    apply res_base_cts_of_cts hπ_cts hπ'_cts hφ_cts hφ _ (V.hopen j),
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
    rw rw_res_base hφ, apply hπ_cts, exact V.hopen j,
  split, simp, simp, exact ⟨hj, heW⟩,
end

lemma res_base_open_map_of_open_map
  (hπ_cts : cts π) (hπ'_cts : cts π')
  (hφ_open : open_map φ) (hφ : π' ∘ φ = π)
  (U : set B) (hU : U ∈ opens B) :
  open_map (res_base hφ U) :=
begin
  apply subtype_map_open, exact hφ_open,
  rw rw_res_base hφ, change (π ⁻¹' U ∈ opens E), apply hπ_cts, exact hU,
end

lemma fiber_map_open_map_iff_res_open_map
  (hπ_cts : cts π) (hπ'_cts : cts π') (hφ : π' ∘ φ = π) :
  open_map φ ↔
  ∀ j, open_map (res_base hφ (V j)) :=
begin
  split,
    intros hφ_open j,
    apply res_base_open_map_of_open_map hπ_cts hπ'_cts hφ_open hφ _ (V.hopen j),
  intros hφ_open_map W hW,
  rw subset_open_iff_open_cover (open_pullback π' hπ'_cts V),
  intro j, change π' ⁻¹' (V j) ∩ φ '' W ∈ opens E',
  specialize hφ_open_map j (to_sub _ W),
  rw to_sub_open_iff at hφ_open_map,
  specialize hφ_open_map ⟨W, hW, rfl⟩,
  rw from_sub_open_iff at hφ_open_map,
  rwa ← from_sub_res_image_of_to_sub,
  apply hπ'_cts, exact V.hopen j,
end

lemma res_base_homeo_of_homeo
  (hπ_cts : cts π) (hπ'_cts : cts π')
  (hφ_homeo : homeo φ) (hφ : π' ∘ φ = π)
  (U : set B) (hU : U ∈ opens B) :
  homeo (res_base hφ U) :=
begin
  rw homeo_iff at *,
  split,
    exact res_base_cts_of_cts hπ_cts hπ'_cts hφ_homeo.1 hφ U hU,
  split,
    exact res_base_bij_of_bij hφ hφ_homeo.2.1 U,
    exact res_base_open_map_of_open_map hπ_cts hπ'_cts hφ_homeo.2.2 hφ U hU,
end

lemma fiber_map_homeo_iff_res_homeo
  (hπ_cts : cts π) (hπ'_cts : cts π') (hφ : π' ∘ φ = π) :
  homeo φ ↔
  ∀ j, homeo (res_base hφ (V j)) :=
begin
  split, intros hφ_homeo j,
    exact res_base_homeo_of_homeo hπ_cts hπ'_cts hφ_homeo hφ (V j) (V.hopen j),
  intro hφ_homeo,
  rw [homeo_iff,
      fiber_map_cts_iff_cover_cts V hπ_cts hπ'_cts hφ,
      fiber_map_bij_iff_cover_bij V.to_cover hφ,
      fiber_map_open_map_iff_res_open_map V hπ_cts hπ'_cts hφ,
      ← forall_and_distrib, ← forall_and_distrib],
  intro j, specialize hφ_homeo j, rwa homeo_iff at hφ_homeo,
end

end fiber_bundle
end fiber_space

section trivial_bundle

variables {E B fiber : Type}
  (π' : E → B)
  (U U' : set B)

structure trivializing_subset {E B : Type} 
  (π' : E → B) (U : set B) (fiber : Type) :=
  (φ : U × fiber → π' ⁻¹' U)
  (hφ : (restrict_target π' U) ∘ φ = prod.fst)

end trivial_bundle