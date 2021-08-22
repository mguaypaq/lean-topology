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

def finsInter_coe {X : Type} (s : finset (set X)) :
  ⋂₀ s = ⋂₀ (s : set (set X)) :=
begin
  ext, split, simp, simp,
end

@[simp] def finsUnion {X : Type} (s : finset (set X)) : set X := 
  {t | ∃ a ∈ s, t ∈ a}
prefix `⋃₀`:110 := finsUnion

def finsUnion_coe {X : Type} (s : finset (set X)) :
  ⋃₀ s = ⋃₀ (s : set (set X)) :=
begin
  ext, split; {intro hx, simp at *, exact hx,},
end

def finsInter_combined {X : Type} (s t : finset (set X)) [decidable_eq (set X)] : 
  ⋂₀ (s ∪ t) = (⋂₀ s) ∩ (⋂₀ t) :=
begin
  rw finsInter_coe s,
  rw finsInter_coe t,
  rw ← set.sInter_union,
  ext, split, simp, simp,
end

-- topology starts here
namespace topology

-- definition of topology and basis
section topology

class topology (X : Type) :=
(opens : set (set X)) -- should this instead be: is_open : set X → Prop ?
(empty_open : ∅ ∈ opens)
(univ_open : set.univ ∈ opens)
(inter₂ : ∀ (U V : set X),
  (U ∈ opens) → (V ∈ opens) → set.inter U V ∈ opens)
(union : ∀ (sU : set (set X)),
  (sU ⊆ opens) → ⋃₀ sU ∈ opens)

parameters {X : Type} [T : topology X] [decidable_eq (set X)]

@[simp] def is_open (U : set X) := U ∈ T.opens

-- can this be given useful coercions? I haven't used this.
def nbhd (x : X) (U : set X) := U ∈ T.opens ∧ x ∈ U

lemma open_of_inter_of_finset (sU : finset (set X)) :
  (↑sU ⊆ T.opens) → ⋂₀ sU ∈ T.opens :=
begin
  intro h_opens,
  induction sU using finset.induction_on with U sU hU1 hU2,
  simp, exact T.univ_open,
  clear hU1,
  simp,
  have U_open := h_opens (finset.mem_insert_self U sU),
  have inter_sU_open := hU2 (set.subset.trans (finset.subset_insert U sU) h_opens),
  have target : {t : X | t ∈ U ∧ ∀ (a : set X), a ∈ sU → t ∈ a} = U.inter (⋂₀ sU),
  finish,
  rw target,
  exact topology.inter₂ U (⋂₀ sU) U_open inter_sU_open,
end

def basis (B : set (set X)) :=
  B ⊆ T.opens ∧ ∀ (U ∈ T.opens) (x ∈ U), ∃ W ∈ B, x ∈ W ∧ W ⊆ U

def pre_basis {Y : Type} (B : set (set Y)) :=
  ⋃₀ B = set.univ ∧ ∀ (U V ∈ B) (x ∈ U ∩ V), ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V

def topology_generated_by_basis {Y : Type} {B : set (set Y)} :
  pre_basis B → (topology Y) :=
begin
  intro h,
  use {U : set Y | ∀ (x ∈ U), ∃ W ∈ B, x ∈ W ∧ W ⊆ U},
  intros x hx, exfalso, exact hx, -- ∅
  intros x hx, rw ← h.1 at hx, -- X
  obtain ⟨W, hW, hxW⟩ := hx,
  use W, split, exact hW, split, exact hxW, simp,
  intros U V hU hV x hx, -- intersections...
  obtain ⟨U0, hU0, hxU0⟩ := hU x hx.1, clear hU,
  obtain ⟨V0, hV0, hxV0⟩ := hV x hx.2, clear hV,
  obtain ⟨W, hW, hxW⟩ := h.2 U0 V0 hU0 hV0 x (by exact ⟨hxU0.1, hxV0.1⟩),
  use W, split, exact hW, split, exact hxW.1,
  suffices : (U0 ∩ V0) ⊆ (U ∩ V),
  apply set.subset.trans hxW.2 this,
  exact set.inter_subset_inter hxU0.2 hxV0.2, -- ... done.
  intros sU hsU x hx, -- unions...
  obtain ⟨U, hU, hxU⟩ := hx,
  obtain ⟨W, hW, hxW⟩ :=  hsU hU x hxU, clear hsU,
  use W, split, exact hW, split, exact hxW.1,
  intros w hw, use U, split, assumption, exact hxW.2 hw, -- ... done.
end

lemma union_of_basis_of_open (B : set (set X)) : basis B → ∀ U ∈ T.opens,
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

def pre_basis_of_subbasis (S : set (set X)) (hS : ⋃₀ S = set.univ) :
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

end topology

section constructing_topology

lemma basis_is_basis_of_generated {Y : Type} {B : set (set Y)} (hB : pre_basis B)
  (heq : decidable_eq (set Y)) : @basis Y (topology_generated_by_basis hB) heq B :=
begin
  split, tauto, tauto,
end

section product_topology

parameters {X Y : Type} (TX : topology X) (TY : topology Y)
  [decidable_eq (set X)] [decidable_eq (set Y)] [decidable_eq (set (X × Y))]

def pre_basis_for_product_topology :
  pre_basis {U : set (X × Y) | ∃ (UX ∈ TX.opens), ∃ (UY ∈ TY.opens),
    (set.prod UX UY) = U} :=
begin
  split, ext, simp, use set.univ, simp,
  use @set.univ X, split, exact TX.univ_open,
  use @set.univ Y, split, exact TY.univ_open,
  clear x TX TY,
  simp,
  rintros U V ⟨UX, hUX, ⟨UY, hUY, hUU⟩⟩ ⟨VX, hVX, ⟨VY, hVY, hVV⟩⟩ p hp,
  use (UX ∩ VX).prod (UY ∩ VY), split,
  use (UX ∩ VX), split,
  exact topology.inter₂ UX VX hUX hVX,
  use (UY ∩ VY), split,
  exact topology.inter₂ UY VY hUY hVY, refl,
  rw [← hUU, ← hVV] at *,
  clear hVX hVY hUX hUY TX TY hUU hVV,
  rw set.prod_inter_prod at *, exact ⟨hp, by tauto⟩,
end

instance product_topology : topology (X × Y) := 
  topology_generated_by_basis (pre_basis_for_product_topology)

lemma basis_around_point (U : set (X × Y)) (hU : U ∈ product_topology.opens) 
  (p : (X × Y)) (hp : p ∈ U) : ∃ (UX ∈ TX.opens), ∃ (UY ∈ TY.opens),
   p ∈ (set.prod UX UY) ∧ (set.prod UX UY) ⊆ U :=
begin
  have h := basis_is_basis_of_generated (pre_basis_for_product_topology TX TY) _,
  obtain ⟨W, ⟨UX, hUX, UY, hUY, hUU⟩, ⟨hpW, hWU⟩⟩ := h.2 U hU p hp,
  use UX, split, exact hUX, use UY, clear h hU, finish, assumption,
end

lemma product_of_bases_is_basis (BX : set (set X)) (BY : set (set Y)) :
  @basis X TX _ BX → @basis Y TY _ BY → 
  @basis (X × Y) product_topology _ 
    {U : set (X × Y) | ∃ (UX ∈ BX), ∃ (UY ∈ BY), (set.prod UX UY) = U} :=
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
  obtain ⟨UX, hUX, ⟨UY, hUY, hp_prod, hprodU⟩⟩ := basis_around_point _ _ U hU p hp,
  obtain ⟨UX', hUX', hUX''⟩ := hBX.2 UX hUX p.fst hp_prod.1,
  obtain ⟨UY', hUY', hUY''⟩ := hBY.2 UY hUY p.snd hp_prod.2,
  use UX'.prod UY', split, rotate,
  split, exact ⟨hUX''.1, hUY''.1⟩,
  apply set.subset.trans _ hprodU,
  exact set.prod_mono hUX''.2 hUY''.2,
  use UX', split, exact hUX', use UY', split, exact hUY', refl,
end

end product_topology

section subspace_topology

-- no need to assume Y is literally a subspace
parameters (X Y : Type) (TX : topology X) (i : Y → X)
  [decidable_eq (set X)] [decidable_eq (set Y)]

def inverse_image_opens := 
  {W : set Y | ∃ (U ∈ TX.opens), W = i ⁻¹' U}

--(inter₂ : ∀ (U V : set X),
--  (U ∈ opens) → (V ∈ opens) → set.inter U V ∈ opens)
--(union : ∀ (sU : set (set X)),
--  (sU ⊆ opens) → ⋃₀ sU ∈ opens)

lemma open_inter_of_preimage (U V : set Y) : 
  U ∈ inverse_image_opens → V ∈ inverse_image_opens → U ∩ V ∈ inverse_image_opens :=
begin
  rintros ⟨U', hU', hU''⟩ ⟨V', hV', hV''⟩,
  exact ⟨U' ∩ V', ⟨topology.inter₂ U' V' hU' hV',
                   by rw [set.preimage_inter, hU'', hV'']⟩⟩,
end

lemma open_union_of_preimage (sU : set (set Y)) : 
  (sU ⊆ inverse_image_opens) → ⋃₀ sU ∈ inverse_image_opens :=
begin
  rintros hsU,
  let sV := {V : set X | V ∈ TX.opens ∧ i ⁻¹' V ∈ sU},
  use ⋃₀ sV,
  split, exact topology.union _ (λ _ hV, hV.1),
  suffices : (set.preimage i) '' sV = sU,
  rw ← this, simp,
  ext U, split, rintro ⟨V, hV, hV'⟩, rw ← hV', exact hV.2,
  intro hU, obtain ⟨V, hV, hV'⟩ := hsU hU,
  use V, split, split, exact hV, rw ← hV', exact hU, rw hV',
end

instance inverse_image_topology : topology Y := ⟨
  inverse_image_opens,
  ⟨∅, ⟨topology.empty_open, by refl⟩⟩,
  ⟨set.univ, ⟨topology.univ_open, by refl⟩⟩,
  open_inter_of_preimage,
  open_union_of_preimage,
⟩

/- 
Should we distinguish between the inverse image topology and the
subspace topology? And how?
-/

end subspace_topology

end constructing_topology

section closed_sets

parameters {X : Type} (TX : topology X) [decidable_eq (set X)]

@[simp] def closed (C : set X) := set.compl C ∈ TX.opens

lemma inter_of_closed (sC : set (set X)) :
  (compl '' sC) ⊆ TX.opens → closed ⋂₀ sC :=
begin
  rw set.sInter_eq_comp_sUnion_compl,
  dsimp, rw compl_compl,
  apply topology.union,
end

lemma union₂_of_closed (C D : set X) : closed C → closed D → closed (C ∪ D) :=
begin
  dsimp, rw set.compl_union C D,
  apply topology.inter₂,
end

lemma closed_of_union_of_finset (sC : finset (set X)) :
  ↑(finset.image compl sC) ⊆ TX.opens → closed ⋃₀ sC :=
begin
  rw finsUnion_coe, dsimp,
  rw set.sUnion_eq_compl_sInter_compl, rw compl_compl,
  rw ← finset.coe_image,
  apply open_of_inter_of_finset,
end

-- closures

def closure (A : set X) := ⋂₀ {C | closed C ∧ A ⊆ C}

lemma closure_is_closed (A : set X) : closed (closure A) :=
begin
  apply inter_of_closed, 
  rw set.compl_image_set_of,
  rw set.set_of_and, simp,
end

lemma self_subset_closure (A : set X) : A ⊆ closure A :=
begin
  unfold closure,
  apply set.subset_sInter, rw set.set_of_and, simp,
end

lemma closure_subset_closed (A C : set X) : closed C ∧ A ⊆ C → closure A ⊆ C :=
begin
  unfold closure, dsimp,
  intro h,
  apply set.sInter_subset_of_mem, assumption,
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
  { apply h.1 (closure TX A),
    exact ⟨closure_is_closed _ A, self_subset_closure _ A⟩,},
  { exact closure_subset_closed _ _ _ h.2,},
end

@[simp]
lemma closure_of_closed (C : set X) (hC: closed C) : closure C = C :=
begin
  symmetry, apply (closure_iff _ C C).mpr,
  simp, exact ⟨hC, by tauto⟩,
end

@[simp]
lemma closure_closure (A : set X) : closure (closure A) = closure A :=
begin
  apply closure_of_closed, apply closure_is_closed,
end

-- interiors
def interior (A : set X)  := ⋃₀ {U : set X | @is_open X TX _ U ∧ U ⊆ A}

-- would it be better to prove the subsequent lemmas
-- from this one + the corresponding closure lemmas?
lemma interior_compl_closure_compl (A : set X) :
  interior A = (closure A.compl).compl :=
begin
  dsimp,
  unfold closure, unfold interior, unfold is_open,
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
  apply topology.union,
  rw set.set_of_and, simp,
end

lemma open_subset_interior (A U : set X) : is_open U ∧ U ⊆ A → U ⊆ interior A :=
begin
  unfold interior, dsimp, intro h,
  apply set.subset_sUnion_of_mem, assumption,
end

lemma interior_subset_self (A : set X) : interior A ⊆ A :=
begin
  unfold interior, dsimp,
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
  apply h.1 (@interior X TX _ A),
  split, apply interior_is_open, apply interior_subset_self,
end

lemma interior_of_open (U : set X) (hU : is_open U) : interior U = U :=
begin
  symmetry, apply (interior_iff _ U U).mpr,
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

def accumulation_point (C : set X) (x : X) [topology X] :=
  (∀ U, nbhd x U → set.nonempty (U ∩ C ∩ {x}ᶜ))

def isolated_point (C : set X) (x : X) [topology X] :=
  ∃ U, nbhd x U ∧ U ∩ C = {x}

lemma mem_interior (A : set X) (x : X) : x ∈ interior A ↔
  (∃ U ∈ TX.opens, x ∈ U ∧ U ⊆ A) :=
begin
  unfold interior, simp, tauto,
end

lemma mem_closure (A : set X) (y : X) : y ∈ closure A ↔ 
  ∀ U ∈ TX.opens, y ∈ U → set.nonempty (U ∩ A) :=
begin
  rw closure_compl_interior_compl,
  rw ← not_iff_not, simp, rw mem_interior,
  conv
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
  unfold accumulation_point,
  intros U hU, unfold nbhd at hU,
  rw mem_closure at hx,
  obtain ⟨y, hy⟩ := hx U hU.1 hU.2,
  use y, split, exact hy, simp, intro hxy, apply h, rw hxy at hy, exact hy.2,
  intro h, cases h with hL hR,
  exact self_subset_closure _ A hL,
  rw mem_closure,
  intros U hU hxU, obtain ⟨y, hy⟩ := hR U ⟨hU, hxU⟩,
  use y, exact hy.1,
end

end closed_sets

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

end topology