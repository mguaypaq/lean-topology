import tactic
import data.set.basic
import data.real.basic

noncomputable theory

/-
Some set theory lemmas I couldn't find using library_search
-- do these already exist?
-- why is the autocomplete not finding all definitions in set and finset?
-- e.g. set.comp doesn't suggest set.compl
-/

@[simp] def finsInter {X : Type} (s : finset (set X)) : set X := 
  {t | ∀ a ∈ s, t ∈ a}
prefix `⋂₀`:110 := finsInter

lemma finsInter_coe {X : Type} (s : finset (set X)) :
  ⋂₀ s = ⋂₀ (s : set (set X)) := by {ext, simp}

@[simp] def finsUnion {X : Type} (s : finset (set X)) : set X := 
  {t | ∃ a ∈ s, t ∈ a}
prefix `⋃₀`:110 := finsUnion

lemma finsUnion_coe {X : Type} (s : finset (set X)) :
  ⋃₀ s = ⋃₀ (s : set (set X)) :=
begin
  ext, split; {intro hx, simp at *, exact hx,},
end

lemma finsInter_combined {X : Type} (s t : finset (set X)) [decidable_eq (set X)] : 
  ⋂₀ (s ∪ t) = (⋂₀ s) ∩ (⋂₀ t) :=
begin
  rw [finsInter_coe s, finsInter_coe t, ← set.sInter_union],
  ext, simp,
end

-- topology starts here
-- definition of topology and basis

class topology (X : Type) :=
(opens [] : set (set X)) -- should this instead be: is_open : set X → Prop ?
(empty_open : ∅ ∈ opens)
(univ_open : set.univ ∈ opens)
(inter₂ : ∀ (U V : set X),
  (U ∈ opens) → (V ∈ opens) → set.inter U V ∈ opens)
(union : ∀ (sU : set (set X)),
  (sU ⊆ opens) → ⋃₀ sU ∈ opens)

namespace topology

variables {X : Type} [topology X]

@[simp]
def is_open (U : set X) := U ∈ opens X

-- can this be given useful coercions? I haven't used this much.
def nbhd (x : X) (U : set X) := U ∈ opens X ∧ x ∈ U

lemma open_of_inter_of_finset [decidable_eq (set X)] (sU : finset (set X)) :
  (↑sU ⊆ opens X) → ⋂₀ sU ∈ opens X :=
begin
  intro h_opens,
  induction sU using finset.induction_on with U sU hU1 hU2,
  simp, exact univ_open,
  clear hU1,
  simp,
  have U_open := h_opens (finset.mem_insert_self U sU),
  have inter_sU_open := hU2 (set.subset.trans (finset.subset_insert U sU) h_opens),
  have target : {t : X | t ∈ U ∧ ∀ (a : set X), a ∈ sU → t ∈ a} = U.inter (⋂₀ sU),
  finish,
  rw target,
  exact inter₂ U (⋂₀ sU) U_open inter_sU_open,
end

lemma open_if_open_around_mem (A : set X) : A ∈ opens X ↔
  ∀ x ∈ A, ∃ U, nbhd x U ∧ U ⊆ A :=
begin
  split, intros hA x hx, use A, exact ⟨⟨hA, hx⟩, by tauto⟩,
  intro hA,
  suffices : A = ⋃₀ {U | U ∈ opens X ∧ U ⊆ A},
  rw this, apply union, rw set.set_of_and, simp,
  ext x, specialize hA x, unfold nbhd at hA, simp at *,
  conv
  begin
    to_rhs, congr, funext,
    rw and_assoc,
    rw and_comm (a ⊆ A) _, rw ← and_assoc,
  end,
  split, exact hA,
  rintro ⟨U, hU⟩, apply hU.2, exact hU.1.2,
end

def basis (B : set (set X)) :=
  B ⊆ opens X ∧ ∀ (U ∈ opens X) (x ∈ U), ∃ W ∈ B, x ∈ W ∧ W ⊆ U

def pre_basis {Y : Type} (B : set (set Y)) :=
  ⋃₀ B = set.univ ∧ ∀ (U V ∈ B) (x ∈ U ∩ V), ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V

def topology_generated_by_basis {Y : Type} {B : set (set Y)}
  (hB : pre_basis B) : (topology Y) :=
⟨ {U : set Y | ∀ (x ∈ U), ∃ W ∈ B, x ∈ W ∧ W ⊆ U},
  λ x hx, false.rec _ hx,
  λ x hx,
    let ⟨W, hW, hxW⟩ := @eq.substr _ _ _ _ hB.1 hx in
    ⟨W, hW, hxW, by simp⟩,
  λ U V hU hV x hx,
    let ⟨U0, hU0, hxU0⟩ := hU x hx.1 in
    let ⟨V0, hV0, hxV0⟩ := hV x hx.2 in
    let ⟨W, hW, hxW⟩ := hB.2 U0 V0 hU0 hV0 x ⟨hxU0.1, hxV0.1⟩ in
    let key := set.inter_subset_inter hxU0.2 hxV0.2 in
    ⟨W, hW, hxW.1, set.subset.trans hxW.2 key⟩,
  λ sU hsU x hx,
    let ⟨U, hU, hxU⟩ := hx in
    let ⟨W, hW, hxW⟩ :=  hsU hU x hxU in
    ⟨W, hW, hxW.1, (λ w hw, ⟨U, hU, hxW.2 hw⟩)⟩,
⟩

lemma union_of_basis_of_open (B : set (set X)) : basis B → ∀ U ∈ opens X,
  U = ⋃₀ {W : set X | W ∈ B ∧ W ⊆ U} :=
begin
  intros hB U hU,
  apply set.subset.antisymm,
  intros x hxU, 
  obtain ⟨W, hW, hxW⟩ := hB.2 U hU x hxU,
  use W, split, exact ⟨hW, hxW.2⟩, exact hxW.1,
  apply set.sUnion_subset,
  intros W hW, exact hW.2,
end

lemma pre_basis_of_subbasis [decidable_eq (set X)]
  (S : set (set X)) (hS : ⋃₀ S = set.univ) :
  pre_basis {W : set X | ∃ sU : finset (set X), ↑sU ⊆ S ∧ W = ⋂₀ sU} :=
begin
  split,
  ext, split, tauto, intro h, rw ← hS at h, clear hS,
  obtain ⟨S0, hS0, hxS0⟩ := h,
  use S0, split, use {S0}, simp, exact hS0, exact hxS0,
  rintros U V ⟨sU, hsU, hsU'⟩ ⟨sV, hsV, hsV'⟩ x hx,
  use U ∩ V, use (sU ∪ sV),
  split, simp, exact ⟨by assumption, by assumption⟩,
  rw hsU', rw hsV',
  clear hsU' hsV' hsU hsV hx x U V hS S,
  rw finsInter_combined,
  split, exact hx, simp,
end

/-
Tried proving this using the definition "an open set is a union of basis elements".
theorem topology_generated_by_basis2 {Y : Type} {B : set (set Y)} :
  pre_basis B → topology Y :=
begin
  intro h,
  -- use {U : set Y | ∀ (x ∈ U), ∃ W ∈ B, x ∈ W ∧ W ⊆ U},
  use {U : set Y | ∃ sU ⊆ B, ⋃₀ sU = U},
  use ∅, simp, -- empty
  simp, use B, rw h.1, simp, -- X
  rintros U V ⟨sU, hsU, hsU'⟩ ⟨sV, hsV, hsV'⟩, -- intersections...
  use {W : set Y | W ∈ B ∧ ∃ (U0 ∈ sU) (V0 ∈ sV), W ⊆ U0 ∩ V0},
  split, intros W hW, exact hW.1,
  ext, split, rintro ⟨W, ⟨hW, ⟨U0, hU0, V0, hV0, hWU0V0⟩⟩, hx⟩,
  split, rw ← hsU', use U0, split, assumption, exact (hWU0V0 hx).1,
  rw ← hsV', use V0, split, assumption, exact (hWU0V0 hx).2,
  rintro ⟨hxU, hxV⟩,
  rw ← hsU' at hxU,
  rw ← hsV' at hxV,
  obtain ⟨U0, hU0, hxU0⟩ := hxU,
  obtain ⟨V0, hV0, hxV0⟩ := hxV,
  obtain ⟨W, hW, hW'⟩ := h.2 U0 V0 (hsU hU0) (hsV hV0) x (by exact ⟨hxU0, hxV0⟩),
  use W, split, split, assumption, use U0, split, assumption, use V0, split,
  assumption, exact hW'.2, exact hW'.1, -- ... done.
  intros sU hsU, -- unions...
  use {W : set Y | W ∈ B ∧ ∃ U ∈ sU, W ⊆ U},
  split, intros W hW, exact hW.1,
  ext, split,
  rintros ⟨W, ⟨⟨hW, ⟨U, hU, hWU⟩⟩, hxW⟩⟩, use U, split, assumption, exact hWU hxW,
  rintro ⟨U, hU, hxU⟩,
  obtain ⟨sV, hsV, hsV'⟩ := hsU hU,
  rw ← hsV' at hxU,
  obtain ⟨W, hW, hxW⟩ := hxU,
  use W, split, split, exact hsV hW, use U, split, exact hU, rw ← hsV',
  intros y hy, use W, split, assumption, assumption, assumption, -- ... done.
end
-/

def discrete_topology (X : Type) : topology X :=
  ⟨set.univ, by trivial, by trivial, λ _ _ _ _, trivial, λ _ _, trivial⟩
def indiscrete_topology {X : Type} : topology X :=
  ⟨{∅, set.univ}, set.mem_insert ∅ {set.univ}, or.inr (set.mem_singleton set.univ),
  begin intros U V hU hV, cases hV,
    rw hV, left, exact set.inter_empty U,
    simp at hV, rw hV, have : U.inter set.univ = U ∩ set.univ, refl, rw this,
    rw set.inter_univ U, exact hU, end,
  begin intros sU hsU, by_cases (set.univ ∈ sU),
    right, simp, ext, simp, exact ⟨set.univ, h, trivial⟩,
    left, simp, intros s hs, cases hsU hs, exact h_1, exfalso,
    simp at h_1, rw h_1 at hs, exact h hs, end⟩


inductive point : Type | p : point
lemma point.is_singleton (x : point) : x = point.p :=
  by {induction x, refl}
lemma point.subset (s : set point) : s = ∅ ∨ s = set.univ :=
  begin by_cases point.p ∈ s,
    right, ext, simp, rw point.is_singleton x, exact h,
    left, ext, simp, rw point.is_singleton x, exact h, end
@[simp] def map_to_point (X : Type) : X → point := λ _, point.p  
@[simp] def map_to_point.val (X : Type) (f : X → point) (x : X) : f x = point.p :=
  by rw point.is_singleton (f x)
def map_to_point.unq (X : Type) (f : X → point) : f = map_to_point X :=
  by {funext, rw point.is_singleton (f x), refl}
instance topology_point : topology point := discrete_topology point


end topology

open topology

section closed_sets

parameters {X : Type} [topology X]

@[simp] def closed (C : set X) := set.compl C ∈ opens X

lemma inter_of_closed (sC : set (set X)) :
  (compl '' sC) ⊆ opens X → closed ⋂₀ sC :=
begin
  rw set.sInter_eq_comp_sUnion_compl,
  dsimp, rw compl_compl,
  apply union,
end

lemma union₂_of_closed (C D : set X) : closed C → closed D → closed (C ∪ D) :=
begin
  dsimp, rw set.compl_union C D,
  apply inter₂,
end

lemma closed_of_union_of_finset [decidable_eq (set X)] (sC : finset (set X)) :
  ↑(finset.image compl sC) ⊆ opens X → closed ⋃₀ sC :=
begin
  rw finsUnion_coe, dsimp,
  rw set.sUnion_eq_compl_sInter_compl, rw compl_compl,
  rw ← finset.coe_image,
  apply open_of_inter_of_finset,
end

-- closures

def closure (A : set X) := ⋂₀ {C | closed C ∧ A ⊆ C}

lemma closure_def (A : set X) : closure A = ⋂₀ {C | closed C ∧ A ⊆ C} := rfl

lemma closure_is_closed (A : set X) : closed (closure A) :=
begin
  apply inter_of_closed, 
  rw set.compl_image_set_of,
  rw set.set_of_and, simp,
end

lemma self_subset_closure (A : set X) : A ⊆ closure A :=
begin
  apply set.subset_sInter, rw set.set_of_and, simp,
end

lemma closure_subset_closed (A C : set X) : closed C ∧ A ⊆ C → closure A ⊆ C :=
begin
  intro h, apply set.sInter_subset_of_mem, assumption,
end

lemma closure_iff (A C' : set X) : C' = closure A ↔ 
  (∀ C, (closed C ∧ A ⊆ C) → C' ⊆ C) ∧ closed C' ∧ A ⊆ C' :=
begin
  split, intro h, rw h, clear h,
  split,
    {apply closure_subset_closed,},
  split,
    {apply closure_is_closed,},
    {apply self_subset_closure,},
  intro h, apply set.subset.antisymm,
  { apply h.1 (closure A),
    exact ⟨closure_is_closed A, self_subset_closure A⟩,},
  { exact closure_subset_closed _ _ h.2,},
end

@[simp]
lemma closure_of_closed (C : set X) (hC: closed C) : closure C = C :=
begin
  symmetry, apply (closure_iff C C).mpr,
  simp, exact ⟨hC, by tauto⟩,
end

@[simp]
lemma closure_closure (A : set X) : closure (closure A) = closure A :=
begin
  apply closure_of_closed, apply closure_is_closed,
end

-- interiors
def interior (A : set X) := ⋃₀ {U : set X | is_open U ∧ U ⊆ A}

lemma interior_def (A : set X) :
  interior A = ⋃₀ {U : set X | is_open U ∧ U ⊆ A} := rfl

-- would it be better to prove the subsequent lemmas
-- from this one + the corresponding closure lemmas?
lemma interior_compl_closure_compl (A : set X) :
  interior A = (closure A.compl).compl :=
begin
  dsimp, rw closure_def, rw interior_def,
  rw set.sInter_eq_comp_sUnion_compl, rw compl_compl,
  rw set.compl_image_set_of, simp,
end

lemma closure_compl_interior_compl (A : set X) :
  closure A = (interior A.compl).compl :=
begin
  rw interior_compl_closure_compl, simp,
end

lemma interior_is_open (A : set X) : is_open (interior A) :=
begin
  apply union,
  rw set.set_of_and, simp,
end

lemma open_subset_interior (A U : set X) : is_open U ∧ U ⊆ A → U ⊆ interior A :=
begin
  dsimp, intro h,
  apply set.subset_sUnion_of_mem, assumption,
end

lemma interior_subset_self (A : set X) : interior A ⊆ A :=
begin
  apply set.sUnion_subset, rw set.set_of_and, simp,
end

lemma interior_iff (A A' : set X) : A' = interior A ↔
  (∀ U, (is_open U ∧ U ⊆ A) → U ⊆ A') ∧ is_open A' ∧ A' ⊆ A :=
begin
  split, intro h, rw h, clear h,
  split,
    { apply open_subset_interior,},
  split,
    { apply interior_is_open,},
    { apply interior_subset_self,},
  intro h, apply set.subset.antisymm,
  apply open_subset_interior, exact h.2,
  apply h.1 (interior A),
  split, apply interior_is_open, apply interior_subset_self,
end

lemma interior_of_open (U : set X) (hU : is_open U) : interior U = U :=
begin
  symmetry, apply (interior_iff U U).mpr,
  simp, exact ⟨hU, by tauto⟩,
  /- here is the proof by taking complements, which seems harder:
  rw interior_compl_closure_compl,
  apply compl_inj_iff.mp, dsimp, rw compl_compl,
  apply closure_of_closed, dsimp, rw compl_compl, exact hU,
  -/
end

@[simp]
lemma interior_interior (A : set X) :
  interior (interior A) = interior A :=
begin
  apply interior_of_open, apply interior_is_open,
end

-- limit points and elementwise properties of closures

def accumulation_point (C : set X) (x : X) :=
  (∀ U, nbhd x U → set.nonempty (U ∩ C ∩ {x}ᶜ))

def isolated_point (C : set X) (x : X) :=
  ∃ U, nbhd x U ∧ U ∩ C = {x}

lemma mem_interior (A : set X) : interior A = 
  {x | ∃ U ∈ opens X, x ∈ U ∧ U ⊆ A} :=
begin
  ext x, rw interior_def, simp, tauto,
end

lemma mem_closure (A : set X) : closure A =
  {y | ∀ U ∈ opens X, y ∈ U → set.nonempty (U ∩ A)} :=
begin
  ext y,
  rw closure_compl_interior_compl,
  rw ← not_iff_not, simp, rw mem_interior,
  conv -- rewrite ¬(U ∩ A).nonempty to U subseteq Aᶜ
  begin
    to_rhs, congr, funext,
    rw set.not_nonempty_iff_eq_empty,
    rw ← set.subset_compl_iff_disjoint,
  end,
  simp,
end

lemma closure_self_union_acc (A : set X) :
  closure A = A ∪ {x | accumulation_point A x} :=
begin
  ext x, split, intro hx, by_cases (x ∈ A), left, assumption, right,
  intros U hU, unfold nbhd at hU,
  rw mem_closure at hx,
  obtain ⟨y, hy⟩ := hx U hU.1 hU.2,
  use y, split, exact hy, simp, intro hxy, apply h, rw hxy at hy, exact hy.2,
  intro h, cases h with hL hR,
  exact self_subset_closure A hL,
  rw mem_closure,
  intros U hU hxU, obtain ⟨y, hy⟩ := hR U ⟨hU, hxU⟩,
  use y, exact hy.1,
end

end closed_sets

section cts_fn

variables {X Y : Type} [topology X] [topology Y]

def cts (f : X → Y) := ∀ V ∈ opens Y, f ⁻¹' V ∈ opens X

lemma cts.id : cts (@id X) := begin intros V hV, exact hV, end

lemma cts_of_comp {Z : Type} [topology Z] (f : X → Y) (g : Y → Z) :
  cts f → cts g → cts (g ∘ f) :=
begin
  intros hf hg W hW, rw set.preimage_comp,
  apply hf, apply hg, exact hW,
end

def ptwise_cts (f : X → Y) (x : X) :=
  ∀ V ∈ opens Y, f x ∈ V → ∃ U ∈ opens X, (f '' U) ⊆ V ∧ x ∈ U

lemma cts_of_closed_iff (f : X → Y) : cts f ↔ 
  ∀ C, closed C → closed (f ⁻¹' C) :=
begin
  split,
  { intros hf C hC,
    simp at *,
    rw ← set.preimage_compl, exact hf Cᶜ hC,},
  { intros hf U hU,
    simp at *,
    specialize hf Uᶜ, rw compl_compl at hf,
    specialize hf hU,
    rwa [set.preimage_compl, compl_compl] at hf,
  },
end

lemma cts_iff_ptwise_cts (f : X → Y) : cts f ↔
  ∀ (x : X), ptwise_cts f x :=
begin
  split,
  { intros hf x V hV hxV,
    exact ⟨f ⁻¹' V, hf V hV, by simp, hxV⟩, },
  { intros hf U hU,
    apply (open_if_open_around_mem _).mpr,
    intros x hx,
    obtain ⟨V, ⟨hV1, hV2, hxV⟩⟩ := hf x U hU hx,
    use V, exact ⟨⟨hV1, hxV⟩, by rwa ← set.image_subset_iff⟩,
    },
end

def cts_iff_cts_on_basis (f : X → Y) (B : set (set Y)) (hB : basis B) :
  cts f ↔ ∀ V, (V ∈ B → f ⁻¹' V ∈ opens X) :=
begin
  split; intros hf V hV,
  exact hf V (hB.1 hV),
  rw union_of_basis_of_open B hB V hV,
  let sY := {W | W ∈ B ∧ W ⊆ V},
  have key : f ⁻¹' ⋃₀ sY = ⋃₀ (set.preimage f '' sY), simp,
  rw key,
  apply union, rw ← set.maps_to',
  intros W hW, exact hf W hW.1,
end

def open_immersion (f : X → Y) := cts f ∧ function.injective f 
  ∧ f '' set.univ ∈ opens Y

def open_map (f : X → Y) := ∀ U ∈ opens X, f '' U ∈ opens Y

lemma map_to_point_cts : cts (map_to_point X) :=
begin
  intros V hV, unfold set.preimage, simp, cases point.subset V; rw h,
  exact empty_open, exact univ_open,
end

end cts_fn

section homeo

variables {X Y Z : Type} [topology X] [topology Y] [topology Z]

def homeo (f : X → Y) :=
  cts f ∧ ∃ (g : Y → X) (hg : cts g),
    function.left_inverse g f ∧ function.right_inverse g f

lemma homeo_iff (f : X → Y) : homeo f ↔
  cts f ∧ function.bijective f ∧ open_map f :=
begin
  split, rintro ⟨hf, g, hg, hg'⟩,
    split, exact hf,
    split, rw function.bijective_iff_has_inverse, exact ⟨g, hg'⟩,
    intros U hU,
    suffices : f '' U = g ⁻¹' U,
    rw this, apply hg, exact hU,
    rw set.image_eq_preimage_of_inverse hg'.1 hg'.2,
  rintro ⟨hf, hbij, hf_open_map⟩,
  split, exact hf,
  obtain ⟨g, hg'⟩ := function.bijective_iff_has_inverse.mp hbij,
  have hg : cts g,
    intros U hU,
    suffices : f '' U = g ⁻¹' U,
    rw ← this, apply hf_open_map, exact hU,
    rw set.image_eq_preimage_of_inverse hg'.1 hg'.2,
  exact ⟨g, hg, hg'⟩,   
end

lemma homeo_comp (f : X → Y) (g : Y → Z) :
  homeo f → homeo g → homeo (g  ∘ f) :=
begin
  rintros ⟨hf, finv, hfinv, hfinv'⟩ ⟨hg, ginv, hginv, hginv'⟩,
  split, exact cts_of_comp f g hf hg,
  use finv ∘ ginv,
  split, exact cts_of_comp ginv finv hginv hfinv,
  exact ⟨function.left_inverse.comp hginv'.1 hfinv'.1,
         function.right_inverse.comp hginv'.2 hfinv'.2⟩,
end

end homeo

section constructing_topology

lemma basis_is_basis_of_generated {Y : Type} {B : set (set Y)} (hB : pre_basis B) :
  @basis Y (topology_generated_by_basis hB) B :=
begin
  split, tauto, tauto,
end

section product_topology

variables {X Y : Type} [topology X] [topology Y]

lemma pre_basis_for_product_topology :
  pre_basis {U : set (X × Y) | ∃ (UX ∈ opens X) (UY ∈ opens Y),
    (set.prod UX UY) = U} :=
begin
  split, ext, simp, use set.univ, simp,
  use set.univ, split, exact univ_open,
  use set.univ, split, exact univ_open,
  simp,
  rintros U V ⟨UX, hUX, ⟨UY, hUY, hUU⟩⟩ ⟨VX, hVX, ⟨VY, hVY, hVV⟩⟩ p hp,
  use (UX ∩ VX).prod (UY ∩ VY), split,
  use (UX ∩ VX), split,
  exact inter₂ UX VX hUX hVX,
  use (UY ∩ VY), split,
  exact inter₂ UY VY hUY hVY, refl,
  rw [← hUU, ← hVV] at *,
  rw set.prod_inter_prod at *, exact ⟨hp, by tauto⟩,
end

instance product_topology : topology (X × Y) := 
  topology_generated_by_basis (pre_basis_for_product_topology)

instance topologies_to_product_topology :
  has_coe ((topology X) × (topology Y)) (topology (X × Y)) :=
  ⟨λ T_pair, product_topology⟩

lemma product_topology.basis :
  basis {U : set (X × Y) | ∃ (UX ∈ opens X) (UY ∈ opens Y),
    (set.prod UX UY) = U} :=
  basis_is_basis_of_generated (pre_basis_for_product_topology)

lemma basis_around_point
  (U : set (X × Y))
  (hU : U ∈ opens (X × Y))
  (p : (X × Y)) (hp : p ∈ U) : 
  ∃ (UX ∈ opens X) (UY ∈ opens Y), p ∈ (set.prod UX UY) ∧ (set.prod UX UY) ⊆ U :=
begin
  have h := basis_is_basis_of_generated pre_basis_for_product_topology,
  obtain ⟨W, ⟨UX, hUX, UY, hUY, hUU⟩, ⟨hpW, hWU⟩⟩ := h.2 U hU p hp,
  use UX, split, exact hUX, use UY, clear h hU,
  split, exact hUY, split, rwa hUU, rwa hUU,
end

lemma prod_of_bases_is_basis (BX : set (set X)) (BY : set (set Y)) :
  basis BX → basis BY → 
  basis {U : set (X × Y) | ∃ (UX ∈ BX) (UY ∈ BY), (set.prod UX UY) = U} :=
begin
  intros hBX hBY,
  split,
  rintros U ⟨UX, hUX, ⟨UY, hUY, hprod⟩⟩,
  intros x hx, use UX.prod UY, split,
  use UX, split, exact hBX.1 hUX,
  use UY, split, exact hBY.1 hUY,
  refl,
  split; rwa hprod,
  intros U hU p hp,
  obtain ⟨UX, hUX, ⟨UY, hUY, hp_prod, hprodU⟩⟩ := basis_around_point U hU p hp,
  obtain ⟨UX', hUX', hUX''⟩ := hBX.2 UX hUX p.fst hp_prod.1,
  obtain ⟨UY', hUY', hUY''⟩ := hBY.2 UY hUY p.snd hp_prod.2,
  use UX'.prod UY', split, rotate,
  split, exact ⟨hUX''.1, hUY''.1⟩,
  apply set.subset.trans _ hprodU,
  exact set.prod_mono hUX''.2 hUY''.2,
  use UX', split, exact hUX', use UY', split, exact hUY', refl,
end

lemma prod_of_opens_is_open
  (U : set X) (hU : U ∈ opens X) (V : set Y) (hV : V ∈ opens Y) :
  (set.prod U V) ∈ opens (X × Y) :=
begin
  intros x hx, exact ⟨set.prod U V, ⟨U, hU, V, hV, by simp⟩, hx, by refl⟩,
end

lemma prod_fst_cts : cts (prod.fst : X × Y → X) :=
begin
  intros UX hUX x hx, use prod.fst ⁻¹' UX,
  split, exact ⟨UX, hUX, set.univ, univ_open, by {ext, simp}⟩,
  tauto,
end

lemma prod_snd_cts : cts (prod.snd : X × Y → Y) :=
begin
  intros UY hUY y hy, use prod.snd ⁻¹' UY,
  split, exact ⟨set.univ, univ_open, UY, hUY, by {ext, simp}⟩,
  tauto,
end

lemma cts_map_to_prod {Z : Type} [topology Z] (f : Z → X × Y) :
  cts f ↔ cts (prod.fst ∘ f) ∧ cts (prod.snd ∘ f) :=
begin
  split, intro hf, split;
  apply cts_of_comp,
    exact hf, apply prod_fst_cts,
    exact hf, apply prod_snd_cts,
  intro hf,
  rw cts_iff_cts_on_basis f _ product_topology.basis,
  simp, rintros V UX hUX UY hUY h, rw ← h,
  have : f ⁻¹' (UX.prod UY) = ((prod.fst ∘ f) ⁻¹' UX) ∩ ((prod.snd ∘ f) ⁻¹' UY),
    ext z, exact iff.rfl, rw this,
  apply inter₂, apply hf.1 _ hUX, apply hf.2 _ hUY,
end

lemma prod_of_cts {Z W : Type} [topology Z] [topology W]
  (f : X → Z) (g : Y → W) (hf : cts f) (hg : cts g) :
  cts (prod.map f g) :=
begin
  rw cts_map_to_prod,
  split; intros V hV; rw set.preimage_comp,
  suffices key : (set.prod (f ⁻¹' V) set.univ) ∈ opens _,
  convert key, ext, simp,
  apply prod_of_opens_is_open, exact hf V hV, exact univ_open,
  suffices key : (set.prod set.univ (g ⁻¹' V)) ∈ opens _,
  convert key, ext, simp,
  apply prod_of_opens_is_open, exact univ_open, exact hg V hV,
end

def diag (X : Type) [topology X] (x : X) : X × X := (x, x)
lemma diag.cts (X : Type) [topology X] : cts (diag X) :=
begin
  rw cts_map_to_prod, exact ⟨cts.id, cts.id⟩,
end

def prod_point_right (X : Type) : X × point ≃ X :=
{ to_fun    := prod.fst,
  inv_fun   := λ x, ⟨x, point.p⟩,
  left_inv  := begin rintro ⟨x, y⟩, simp, rw point.is_singleton y, end,
  right_inv := λ x, rfl }

lemma prod_point_right.cts (X : Type) [topology X] :
  cts (prod_point_right X).to_fun := prod_fst_cts

lemma prod_point_right.inv_cts (X : Type) [topology X] :
  cts (prod_point_right X).inv_fun :=
begin
  rw cts_map_to_prod, split,
  exact cts.id, exact map_to_point_cts,
end

def prod_point_left (X : Type) : point × X ≃ X :=
{ to_fun    := prod.snd,
  inv_fun   := λ x, ⟨point.p, x⟩,
  left_inv  := begin rintro ⟨y, x⟩, simp, rw point.is_singleton y, end,
  right_inv := λ x, rfl }

lemma prod_point_left.cts (X : Type) [topology X] :
  cts (prod_point_left X).to_fun := prod_snd_cts

lemma prod_point_left.inv_cts (X : Type) [topology X] :
  cts (prod_point_left X).inv_fun :=
begin
  rw cts_map_to_prod, split,
  exact map_to_point_cts, exact cts.id,
end

end product_topology

section inverse_image_topology

-- consider generalizing to "limit topology"?

variables {X Y : Type} [topology X] (i : Y → X)

@[simp]
def inverse_image_opens := 
  --{W : set Y | ∃ (U ∈ opens X), W = i ⁻¹' U}
  set.preimage i '' opens X

lemma inverse_image_open_of_open (U : set X) :
  U ∈ opens X → i ⁻¹' U ∈ inverse_image_opens i :=
begin
  simp, intro hU, exact ⟨U, hU, by simp⟩,
end

lemma open_inter_of_preimage (U V : set Y) : 
  U ∈ inverse_image_opens i → V ∈ inverse_image_opens i →
  U ∩ V ∈ inverse_image_opens i :=
begin
  rintros ⟨U', hU', hU''⟩ ⟨V', hV', hV''⟩,
  exact ⟨U' ∩ V', ⟨inter₂ U' V' hU' hV',
                   by rw [set.preimage_inter, hU'', hV'']⟩⟩,
end

lemma open_union_of_preimage (sU : set (set Y)) : 
  (sU ⊆ inverse_image_opens i) → ⋃₀ sU ∈ inverse_image_opens i :=
begin
  rintros hsU,
  let sV := {V : set X | V ∈ opens X ∧ i ⁻¹' V ∈ sU},
  use ⋃₀ sV,
  split, exact union _ (λ _ hV, hV.1),
  suffices : (set.preimage i) '' sV = sU,
  rw ← this, simp,
  ext U, split, rintro ⟨V, hV, hV'⟩, rw ← hV', exact hV.2,
  intro hU, obtain ⟨V, hV, hV'⟩ := hsU hU,
  use V, split, split, exact hV, rw hV', exact hU, exact hV',
end

def inverse_image_topology : topology Y := ⟨
  inverse_image_opens i,
  ⟨∅, ⟨empty_open, rfl⟩⟩,
  ⟨set.univ, ⟨univ_open, rfl⟩⟩,
  open_inter_of_preimage i,
  open_union_of_preimage i,
⟩

lemma pullback_cts_along_inverse_image (Z : Type) [topology Z] (f : X → Z):
  cts f → @cts _ _ (inverse_image_topology i) _ (f ∘ i) :=
begin
  intros hf V hV,
  change i ⁻¹' (f ⁻¹' V) ∈ opens _,
  apply inverse_image_open_of_open, exact hf V hV,
end

end inverse_image_topology

section subspace_topology

variables {X : Type} (A : set X)

@[simp] def to_sub : set X → set A := set.preimage coe
@[simp] def from_sub : set A → set X := set.image coe

def incl_of_subsets {U U' : set X} (hU' : U' ⊆ U) : U' → U :=
  subtype.map (@id X) hU'

def restrict_cod {Y : Type} (f : X → Y) {p : Y → Prop}
  (h : ∀ (x : X), p (f x)) : X → (subtype p) :=
  subtype.coind f h

def restrict_target {Y : Type} (f : X → Y)
  (U : set Y) : f ⁻¹' U → U :=
  subtype.map f (by simp)

lemma to_sub_eq_inter (V : set X) : to_sub A V = to_sub A (A ∩ V) := by simp
lemma from_sub_subset_self (U : set A) : from_sub A U ⊆ A := by simp

@[simp]
lemma from_sub_to_sub_eq_inter (V : set X) : from_sub A (to_sub A V) = A ∩ V :=
begin
  ext x, simp, tauto,
end

@[simp]
lemma to_sub_from_sub_eq_self (U : set A) : to_sub A (from_sub A U) = U :=
begin
  ext x, simp,
end

@[simp]
lemma image_of_from_sub {Y : Type} (f : X → Y) (U : set A) :
  subtype.restrict f A '' U = f '' from_sub A U :=
begin
  ext y, split; simp; tauto,
end

@[simp]
lemma image_of_to_sub {Y : Type} (f : X → Y) (U : set X) :
  subtype.restrict f A '' to_sub A U = f '' (A ∩ U) :=
begin
  ext y, split; simp; tauto,
end

variables {Y : Type} {p : X → Prop} {q : Y → Prop}
  (f : X → Y) (hf : ∀ (x : X), p x → q (f x))

variable [topology X]

instance subtype_topology (p : X → Prop) : topology (subtype p) :=
  inverse_image_topology (coe : (subtype p) → X)

instance subspace_topology : topology A := subtype_topology A

lemma to_sub_open_iff (U' : set A) :
  U' ∈ opens A ↔ ∃ U ∈ opens X, U' = to_sub A U :=
begin
  split, rintros ⟨U', hU', hU⟩, tauto, rintro ⟨U, hU, hU'⟩,
  rw hU', simp, apply inverse_image_open_of_open, exact hU,
end

lemma from_sub_open_iff (hA : A ∈ opens X) (U' : set A) :
  U' ∈ opens A ↔ from_sub A U' ∈ opens X :=
begin
  rw to_sub_open_iff, split,
  { rintro ⟨U, hU, hU'⟩,  rw [hU', from_sub_to_sub_eq_inter],
    exact inter₂ _ _ hA hU},
  intro h, use from_sub A U', rw to_sub_from_sub_eq_self, exact ⟨h, by simp⟩,
end

lemma cts_at_pt_of_open {Y : Type} [topology Y]
  (f : X → Y)
  (U : set X) (hU : U ∈ opens X)
  (x : X) (hxU : x ∈ U) :
  ptwise_cts f x ↔
  @ptwise_cts _ _ (subspace_topology U) _ (subtype.restrict f U) ⟨x, hxU⟩ :=
begin
  split;
  intros hf V hV hfxV;
  obtain ⟨U', hU', hU'V, hxU'⟩ := hf V hV hfxV,
  use (to_sub U U'),
  split, simp,
  rw to_sub_open_iff, exact ⟨U', hU', by simp⟩,
  split, rw image_of_to_sub,
  exact set.subset.trans (set.image_subset f (set.inter_subset_right U U')) hU'V,
  exact hxU',
  use from_sub U U',
  split, rw ← from_sub_open_iff U hU, exact hU',
  split, rw ← image_of_from_sub, exact hU'V,
  simp, exact ⟨hxU, hxU'⟩,
end

lemma coe_cts {U : set X} : cts (coe : U → X) :=
begin
  intros V hV, exact ⟨V, hV, rfl⟩,
end

lemma coe_cts' {p : X → Prop} : cts (coe : (subtype p) → X) :=
begin
  intros V hV, exact ⟨V, hV, rfl⟩,
end


lemma restrict_cod_cts {Y : Type} [topology Y] {f : X → Y}
  {U : set Y} {hU : ∀ (x : X), U (f x)} (hf : cts f) :
  cts (restrict_cod f hU) :=
begin
  rintros V ⟨W, hW⟩,
  suffices : restrict_cod f hU ⁻¹' V = f ⁻¹' W,
    rw this, exact hf W hW.1,
  ext, unfold restrict_cod, rw ← hW.2, simp,
end

lemma subtype_map_cts {Y : Type} [topology Y] {f : X → Y} (hf : cts f)
  {p : X → Prop} {q : Y → Prop} {h : ∀ (x : X), p x → q (f x)} :
  cts (subtype.map f h) :=
begin
  rintros V ⟨W, hW, hW'⟩, rw ← hW',
  exact ⟨f ⁻¹' W, hf W hW, rfl⟩,
end

lemma incl_of_subsets_cts {U U' : set X} {hU' : U' ⊆ U} :
  cts (incl_of_subsets hU') :=
begin
  apply subtype_map_cts, intro V, exact id,
end

lemma restrict_target_cts {Y : Type} [topology Y] {f : X → Y}
  {U : set Y} (hf : cts f) : cts (restrict_target f U) :=
begin
  apply subtype_map_cts hf,
  /-
  -- alternate proof:
  apply restrict_cod_cts,
  apply cts_of_comp,
  apply coe_cts,
  exact hf,
  -/
end

lemma subtype_map_open {Y : Type} [topology Y] {f : X → Y}
  (hf : open_map f)
  {p : X → Prop} {q : Y → Prop} (hp : p ∈ opens X)
  {hpq : ∀ (x : X), p x → q (f x)} :
  open_map (subtype.map f hpq) :=
begin
  rintros V ⟨W, hW, hW'⟩, rw ← hW',
  have : subtype.map f hpq '' (coe ⁻¹' W) = coe ⁻¹' (f '' (p ∩ W)),
    ext ⟨y, hy⟩, unfold subtype.map, simp,
    conv begin to_rhs, congr, funext, rw and_assoc, end, refl,
  rw this,
  apply coe_cts, apply hf, apply inter₂ _ _ hp hW,
end

example {X Y : Type} [topology X] [topology Y] {f : X → Y} (hf : cts f) :
  let g : @set.univ X → @set.univ Y := λ x, subtype.mk (f x) trivial in
  cts g :=
begin
  intro g,
  suffices : g = restrict_target f set.univ,
    rw this, apply restrict_target_cts hf,
  ext ⟨x, hx⟩, unfold restrict_target, simp,
end

  
end subspace_topology

end constructing_topology

-- example:
-- ℝ with the standard topology
def ball (x ε : ℝ) := {y : ℝ | abs (y-x) < ε}

lemma subset_of_le_eps_ball
  (r1 r2 : ℝ) (h : r1 ≤ r2) (x : ℝ) : 
  set.subset (ball x r1) (ball x r2) :=
begin
  intros y hy,
  unfold ball at *, simp at *, linarith,
end

lemma subset_of_lt_eps_ball
  (r1 r2 : ℝ) (h : r1 < r2) (x : ℝ) : 
  set.subset (ball x r1) (ball x r2) :=
begin
  apply subset_of_le_eps_ball, linarith,
end

def standard_opens_ℝ := 
  {U : set ℝ | ∀ x ∈ U, ∃ ε > 0, set.subset (ball x ε) U}

lemma standard_basis_ℝ : pre_basis {W : set ℝ | ∃ x ε, W = ball x ε } :=
begin
  split,
  ext, simp, use ball x 1, use x, use 1, unfold ball, simp,
  rintros U V ⟨u, εu, hU⟩ ⟨v, εv, hV⟩ x hx,
  let r := min (εu - abs (x - u)) (εv - abs (x - v)),
  simp, use ball x r, use x, use r, unfold ball at *,
  rw hU at *, rw hV at *, clear hU hV,
  obtain ⟨hx1, hx2⟩ := hx, simp at *,
  split, split, assumption, assumption,
  split; intros a ha1 ha2,
  linarith [abs_sub_le a x u],
  linarith [abs_sub_le a x v],
end

instance standard_topology_ℝ : topology ℝ :=
  topology_generated_by_basis standard_basis_ℝ