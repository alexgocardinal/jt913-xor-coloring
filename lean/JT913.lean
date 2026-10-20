import Mathlib

/-!
# Jensen--Toft 9.13: the power-of-two family

Definitions and proofs for the XOR construction.
The final theorem is conventionalTheorem_verified.
Audit.lean checks its explicit statement and axiom dependencies.
-/

namespace JT913

/-- The vertices of a generalized Kneser graph on a finite ground type. -/
abbrev UniformSet (α : Type*) (k : ℕ) := { S : Finset α // S.card = k }

/-- Distinct uniform sets are adjacent if their intersection is too small.
The explicit inequality of vertices makes this a simple graph even when
`t > k`; the Jensen--Toft range has `0 < t < k`. -/
noncomputable def generalizedKneser (α : Type*) [DecidableEq α]
    (k t : ℕ) : SimpleGraph (UniformSet α k) := by
  classical
  refine
    { Adj := fun S T => S ≠ T ∧ (S.1 ∩ T.1).card < t
      symm := ?_
      loopless := ?_ }
  · constructor
    intro S T h
    exact ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩
  · constructor
    intro S h
    exact h.1 rfl

/-- The graph `K(n,k,t)` in the conventional labelling. -/
noncomputable abbrev K (n k t : ℕ) : SimpleGraph (UniformSet (Fin n) k) :=
  generalizedKneser (Fin n) k t

/-- Binary vectors provide all `2^m` distinct ground labels. -/
abbrev Label (m : ℕ) := Fin m → ZMod 2

/-- The vertices of `K(2k,k,k-1)` for `k = 2^r`.
The parameter `r` must be positive to belong to the original `t > 0` range. -/
abbrev MiddleVertex (r : ℕ) := UniformSet (Label (r + 1)) (2 ^ r)

noncomputable def middleGraph (r : ℕ) : SimpleGraph (MiddleVertex r) := by
  classical
  exact generalizedKneser (Label (r + 1)) (2 ^ r) (2 ^ r - 1)

/-- The vector sum, equivalently bitwise XOR, of all labels in `S`. -/
noncomputable def syndrome (r : ℕ) (S : Finset (Label (r + 1))) :
    Label (r + 1) := S.sum id

/-- Toggle the ground element whose label equals the XOR of the set. -/
noncomputable def xorColor (r : ℕ) (S : MiddleVertex r) :
    Finset (Label (r + 1)) := by
  classical
  exact (symmDiff S.1 {syndrome r S.1})

/-- The actual fiber of a proposed color; membership makes no assumption
about which finite sets happen to be attained as colors. -/
noncomputable def fiber (r : ℕ) (T : Finset (Label (r + 1))) :
    Finset (MiddleVertex r) := by
  classical
  exact (Finset.univ : Finset (MiddleVertex r)).filter (fun S => xorColor r S = T)

/-- The image of the explicit color assignment. -/
noncomputable def usedColors (r : ℕ) :
    Finset (Finset (Label (r + 1))) := by
  classical
  exact (Finset.univ : Finset (MiddleVertex r)).image (xorColor r)

/-- The vector-labelled ground set has `2k` elements. -/
def GroundCardObligation (r : ℕ) : Prop :=
  Fintype.card (Label (r + 1)) = 2 * 2 ^ r

/-- The middle layer has the expected binomial cardinality. -/
def MiddleLayerCardObligation (r : ℕ) : Prop :=
  Fintype.card (MiddleVertex r) = Nat.choose (2 * 2 ^ r) (2 ^ r)

/-- Intended checksum lemma: toggling the checksum makes it zero. -/
def ChecksumObligation (r : ℕ) : Prop :=
  ∀ S : MiddleVertex r, syndrome r (xorColor r S) = 0

/-- Intended fiber characterization, including both stars and tops. -/
def FiberObligation (r : ℕ) : Prop :=
  ∀ (T : Finset (Label (r + 1))) (S : MiddleVertex r),
    syndrome r T = 0 →
    (xorColor r S = T ↔ (symmDiff S.1 T).card = 1)

/-- Each color that occurs has exactly `k+1` vertices. -/
def FiberSizeObligation (r : ℕ) : Prop :=
  ∀ T ∈ usedColors r, (fiber r T).card = 2 ^ r + 1

/-- The XOR assignment is proper for the actual graph definition. -/
def ProperColorObligation (r : ℕ) : Prop :=
  ∀ S T : MiddleVertex r,
    (middleGraph r).Adj S T → xorColor r S ≠ xorColor r T

/-- The maximum independent-set inequality used for the lower bound.
An independent family has no pair of adjacent vertices. -/
def IndependenceBoundObligation (r : ℕ) : Prop :=
  ∀ A : Finset (MiddleVertex r),
    (∀ S ∈ A, ∀ T ∈ A, ¬(middleGraph r).Adj S T) →
    A.card ≤ 2 ^ r + 1

/-- Exact intended theorem. `chromaticNumber` in mathlib takes values in
`ℕ∞`, so the finite integer on the right is explicitly coerced.  The
restriction `r ≥ 1` enforces Jensen--Toft's `t > 0`. -/
def MainTheoremObligation (r : ℕ) : Prop :=
  1 ≤ r →
    (middleGraph r).chromaticNumber =
      (((Nat.choose (2 * (2 ^ r)) (2 ^ r)) / (2 ^ r + 1) : ℕ) : ℕ∞)

/-- Transfer to the conventional labels `Fin (2k)` requires a bijection of
ground sets and the induced graph isomorphism. This is the final statement
matching the notation `K(2k,k,k-1)` literally. -/
def ConventionalTheoremObligation (r : ℕ) : Prop :=
  1 ≤ r →
    (K (2 * 2 ^ r) (2 ^ r) (2 ^ r - 1)).chromaticNumber =
      (((Nat.choose (2 * (2 ^ r)) (2 ^ r)) / (2 ^ r + 1) : ℕ) : ℕ∞)


theorem groundCard_verified (r : ℕ) : GroundCardObligation r := by
  simp [GroundCardObligation, Label,
    pow_succ, Nat.mul_comm]


theorem middleLayerCard_verified (r : ℕ) :
    MiddleLayerCardObligation r := by
  change Fintype.card {S : Finset (Label (r + 1)) // S.card = 2 ^ r} =
    Nat.choose (2 * 2 ^ r) (2 ^ r)
  rw [Fintype.card_finset_len]
  have h : Fintype.card (Label (r + 1)) = 2 * 2 ^ r :=
    groundCard_verified r
  rw [h]


theorem checksum_verified (r : ℕ) : ChecksumObligation r := by
  classical
  intro S
  let x := syndrome r S.1
  have hx : x + x = 0 := by
    ext i
    exact ZModModule.add_self (x i)
  change (symmDiff S.1 {x}).sum id = 0
  by_cases h : x ∈ S.1
  · have ht : symmDiff S.1 {x} = S.1.erase x := by
      ext a
      simp [symmDiff_def]; aesop
    rw [ht]
    have hs : (S.1.erase x).sum id + x = x := by
      simpa [x, syndrome] using (Finset.sum_erase_add S.1 id h)
    have hz := congrArg (fun y => y - x) hs
    simpa using hz
  · have ht : symmDiff S.1 {x} = insert x S.1 := by
      ext a
      simp [symmDiff_def]; aesop
    rw [ht, Finset.sum_insert h]
    change x + x = 0
    exact hx


theorem xorColor_card_verified (r : ℕ) (S : MiddleVertex r) :
    (xorColor r S).card + 1 = 2 ^ r ∨
    (xorColor r S).card = 2 ^ r + 1 := by
  classical
  let x := syndrome r S.1
  by_cases h : x ∈ S.1
  · left
    have ht : symmDiff S.1 {x} = S.1.erase x := by
      ext a
      simp [symmDiff_def]; aesop
    change (symmDiff S.1 {x}).card + 1 = 2 ^ r
    rw [ht, Finset.card_erase_of_mem h, S.property]
    have hp : 0 < 2 ^ r := by positivity
    omega
  · right
    have ht : symmDiff S.1 {x} = insert x S.1 := by
      ext a
      simp [symmDiff_def]; aesop
    change (symmDiff S.1 {x}).card = 2 ^ r + 1
    rw [ht]
    simp [h, S.property]


theorem xorColor_recover_verified (r : ℕ) (S : MiddleVertex r) :
    symmDiff (xorColor r S) {syndrome r S.1} = S.1 := by
  classical
  simp [xorColor]

theorem xorColor_distance_verified (r : ℕ) (S : MiddleVertex r) :
    (symmDiff S.1 (xorColor r S)).card = 1 := by
  classical
  simp [xorColor]


theorem syndrome_toggle_verified (r : ℕ)
    (A : Finset (Label (r + 1))) (x : Label (r + 1)) :
    syndrome r (symmDiff A {x}) = syndrome r A + x := by
  classical
  have hx : x + x = 0 := by
    ext i
    exact ZModModule.add_self (x i)
  change (symmDiff A {x}).sum id = A.sum id + x
  by_cases h : x ∈ A
  · have ht : symmDiff A {x} = A.erase x := by
      ext a
      simp [symmDiff_def]; aesop
    rw [ht]
    have hs : (A.erase x).sum id + x = A.sum id :=
      Finset.sum_erase_add A id h
    have hz := congrArg (fun y => y + x) hs
    simpa only [add_assoc, hx, add_zero] using hz
  · have ht : symmDiff A {x} = insert x A := by
      ext a
      simp [symmDiff_def]; aesop
    rw [ht, Finset.sum_insert h]
    exact add_comm _ _


theorem fiber_verified (r : ℕ) : FiberObligation r := by
  classical
  intro T S hT
  constructor
  · intro h
    rw [← h]
    exact xorColor_distance_verified r S
  · intro h
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
    have hST : T = symmDiff S.1 {x} := by
      have hh := congrArg
        (fun A : Finset (Label (r + 1)) => symmDiff S.1 A) hx
      simpa using hh
    have hS : S.1 = symmDiff T {x} := by
      rw [hST]
      simp
    have hs : syndrome r S.1 = x := by
      rw [hS, syndrome_toggle_verified, hT, zero_add]
    change symmDiff S.1 {syndrome r S.1} = T
    rw [hs, hS]
    simp


theorem properColor_verified (r : ℕ) : ProperColorObligation r := by
  classical
  intro S T hadj hc
  let x := syndrome r S.1
  let y := syndrome r T.1
  have hm : ∀ (A : Finset (Label (r + 1))) (z : Label (r + 1)),
      z ∈ A → symmDiff A {z} = A.erase z := by
    intro A z hz
    ext a
    simp [symmDiff_def]; aesop
  have hn : ∀ (A : Finset (Label (r + 1))) (z : Label (r + 1)),
      z ∉ A → symmDiff A {z} = insert z A := by
    intro A z hz
    ext a
    simp [symmDiff_def]; aesop
  change symmDiff S.1 {x} = symmDiff T.1 {y} at hc
  have hbad : (S.1 ∩ T.1).card < 2 ^ r - 1 := hadj.2
  have hS := S.property
  have hT := T.property
  by_cases hx : x ∈ S.1
  · by_cases hy : y ∈ T.1
    · rw [hm S.1 x hx, hm T.1 y hy] at hc
      have hsub : S.1.erase x ⊆ S.1 ∩ T.1 := by
        intro a ha
        have haS : a ∈ S.1 := (Finset.mem_erase.mp ha).2
        have haT : a ∈ T.1 :=
          (Finset.mem_erase.mp (hc ▸ ha)).2
        exact Finset.mem_inter.mpr ⟨haS, haT⟩
      have hb := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hx, hS] at hb
      omega
    · rw [hm S.1 x hx, hn T.1 y hy] at hc
      have hh := congrArg Finset.card hc
      simp [Finset.card_erase_of_mem hx, hy, hS, hT] at hh
  · by_cases hy : y ∈ T.1
    · rw [hn S.1 x hx, hm T.1 y hy] at hc
      have hh := congrArg Finset.card hc
      simp [Finset.card_erase_of_mem hy, hx, hS, hT] at hh; omega
    · rw [hn S.1 x hx, hn T.1 y hy] at hc
      have hsub : S.1 ∪ T.1 ⊆ insert x S.1 := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact Finset.mem_insert_of_mem ha
        · rw [hc]
          exact Finset.mem_insert_of_mem ha
      have hb := Finset.card_le_card hsub
      have he := Finset.card_union_add_card_inter S.1 T.1
      have hi : (insert x S.1).card = 2 ^ r + 1 := by
        simp [hx, hS]
      rw [hi] at hb
      omega


theorem fiber_toggle_count_verified (r : ℕ)
    (T : Finset (Label (r + 1))) (hT : syndrome r T = 0) :
    (fiber r T).card =
      ((Finset.univ : Finset (Label (r + 1))).filter
        (fun x => (symmDiff T {x}).card = 2 ^ r)).card := by
  classical
  let D := (Finset.univ : Finset (Label (r + 1))).filter
    (fun x => (symmDiff T {x}).card = 2 ^ r)
  let f : ∀ x ∈ D, MiddleVertex r :=
    fun x hx => ⟨symmDiff T {x}, (Finset.mem_filter.mp hx).2⟩
  change (fiber r T).card = D.card
  refine (Finset.card_bij (s := D) (t := fiber r T) f ?_ ?_ ?_).symm
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (fiber_verified r T (f x hx) hT).2
    change (symmDiff (symmDiff T {x}) T).card = 1
    rw [symmDiff_comm (symmDiff T {x}) T]
    simp
  · intro x hx y hy he
    have hh := congrArg
      (fun S : MiddleVertex r => syndrome r S.1) he
    change syndrome r (symmDiff T {x}) =
      syndrome r (symmDiff T {y}) at hh
    simpa only [syndrome_toggle_verified, hT, zero_add] using hh
  · intro S hS
    have hc : xorColor r S = T := by
      simpa [fiber] using hS
    let x := syndrome r S.1
    have he : symmDiff T {x} = S.1 := by
      rw [← hc]
      exact xorColor_recover_verified r S
    have hx : x ∈ D := by
      change x ∈ (Finset.univ : Finset (Label (r + 1))).filter
        (fun z => (symmDiff T {z}).card = 2 ^ r)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [he]
      exact S.property
    refine ⟨x, hx, ?_⟩
    apply Subtype.ext
    exact he


theorem fiberSize_verified (r : ℕ) : FiberSizeObligation r := by
  classical
  intro T hused
  have hex : ∃ S : MiddleVertex r, xorColor r S = T := by
    simpa [usedColors] using hused
  obtain ⟨S, hS⟩ := hex
  have hzero : syndrome r T = 0 := by
    rw [← hS]
    exact checksum_verified r S
  rw [fiber_toggle_count_verified r T hzero]
  let D := (Finset.univ : Finset (Label (r + 1))).filter
    (fun x => (symmDiff T {x}).card = 2 ^ r)
  change D.card = 2 ^ r + 1
  have hcard : ∀ x : Label (r + 1),
      (symmDiff T {x}).card =
        if x ∈ T then T.card - 1 else T.card + 1 := by
    intro x
    by_cases hx : x ∈ T
    · have he : symmDiff T {x} = T.erase x := by
        ext a
        simp [symmDiff_def]; aesop
      rw [he]
      simp [hx, Finset.card_erase_of_mem hx]
    · have he : symmDiff T {x} = insert x T := by
        ext a
        simp [symmDiff_def]; aesop
      rw [he]
      simp [hx]
  rcases xorColor_card_verified r S with hs | hs
  · rw [hS] at hs
    have hD : D = Tᶜ := by
      ext x
      change (x ∈ (Finset.univ : Finset (Label (r + 1))).filter
        (fun z => (symmDiff T {z}).card = 2 ^ r)) ↔ x ∈ Tᶜ
      simp only [Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_compl]
      rw [hcard]
      by_cases hx : x ∈ T <;> simp [hx] <;> omega
    rw [hD, Finset.card_compl]
    have hg : Fintype.card (Label (r + 1)) = 2 * 2 ^ r :=
      groundCard_verified r
    rw [hg]
    omega
  · rw [hS] at hs
    have hD : D = T := by
      ext x
      change (x ∈ (Finset.univ : Finset (Label (r + 1))).filter
        (fun z => (symmDiff T {z}).card = 2 ^ r)) ↔ x ∈ T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcard]
      by_cases hx : x ∈ T <;> simp [hx] <;> omega
    rw [hD]
    exact hs


theorem colorPartitionCount_verified (r : ℕ) :
    Fintype.card (MiddleVertex r) =
      (usedColors r).card * (2 ^ r + 1) := by
  classical
  calc
    Fintype.card (MiddleVertex r) =
        ∑ T ∈ usedColors r, (fiber r T).card := by
      simpa [usedColors, fiber] using
        (Finset.card_eq_sum_card_image (xorColor r)
          (Finset.univ : Finset (MiddleVertex r)))
    _ = ∑ _T ∈ usedColors r, (2 ^ r + 1) := by
      apply Finset.sum_congr rfl
      intro T hT
      exact fiberSize_verified r T hT
    _ = (usedColors r).card * (2 ^ r + 1) := by
      simp [Nat.mul_comm]

theorem usedColorsCard_verified (r : ℕ) :
    (usedColors r).card =
      Nat.choose (2 * 2 ^ r) (2 ^ r) / (2 ^ r + 1) := by
  have h : Nat.choose (2 * 2 ^ r) (2 ^ r) =
      (usedColors r).card * (2 ^ r + 1) := by
    calc
      Nat.choose (2 * 2 ^ r) (2 ^ r) =
          Fintype.card (MiddleVertex r) :=
        (middleLayerCard_verified r).symm
      _ = (usedColors r).card * (2 ^ r + 1) :=
        colorPartitionCount_verified r
  rw [h]
  simp


theorem independent_intersection_verified (r : ℕ)
    (A : Finset (MiddleVertex r))
    (hA : ∀ S ∈ A, ∀ T ∈ A, ¬(middleGraph r).Adj S T)
    (S : MiddleVertex r) (hS : S ∈ A)
    (T : MiddleVertex r) (hT : T ∈ A) :
    2 ^ r - 1 ≤ (S.1 ∩ T.1).card := by
  classical
  by_cases he : S = T
  · subst T
    simp [S.property]
  · by_contra h
    apply hA S hS T hT
    exact ⟨he, by omega⟩

theorem independent_distinct_intersection_verified (r : ℕ)
    (A : Finset (MiddleVertex r))
    (hA : ∀ S ∈ A, ∀ T ∈ A, ¬(middleGraph r).Adj S T)
    (S : MiddleVertex r) (hS : S ∈ A)
    (T : MiddleVertex r) (hT : T ∈ A) (hne : S ≠ T) :
    (S.1 ∩ T.1).card = 2 ^ r - 1 := by
  classical
  have hlo := independent_intersection_verified r A hA S hS T hT
  have hcS := S.property
  have hcT := T.property
  have hlt : (S.1 ∩ T.1).card < 2 ^ r := by
    by_contra hh
    have hi : S.1 ∩ T.1 = S.1 :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hsub : S.1 ⊆ T.1 := by
      intro x hx
      have hx' : x ∈ S.1 ∩ T.1 := by
        rw [hi]
        exact hx
      exact (Finset.mem_inter.mp hx').2
    have he : S.1 = T.1 :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    exact hne (Subtype.ext he)
  omega


theorem nearby_star_or_top_verified {α : Type*} [DecidableEq α]
    (k : ℕ) (S T X : Finset α)
    (hX : X.card = k)
    (hST : (S ∩ T).card + 1 = k)
    (hSX : k - 1 ≤ (S ∩ X).card)
    (hTX : k - 1 ≤ (T ∩ X).card) :
    S ∩ T ⊆ X ∨ X ⊆ S ∪ T := by
  classical
  by_cases hcore : S ∩ T ⊆ X
  · exact Or.inl hcore
  · right
    have hp : ((S ∩ T) ∩ X).card < (S ∩ T).card := by
      by_contra hh
      have heq : (S ∩ T) ∩ X = S ∩ T :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left
          (by omega)
      apply hcore
      intro a ha
      have ha' : a ∈ (S ∩ T) ∩ X := by
        rw [heq]
        exact ha
      exact (Finset.mem_inter.mp ha').2
    have hu : (S ∩ X) ∪ (T ∩ X) = (S ∪ T) ∩ X := by
      ext a
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    have hi : (S ∩ X) ∩ (T ∩ X) = (S ∩ T) ∩ X := by
      ext a
      simp only [Finset.mem_inter]
      tauto
    have he := Finset.card_union_add_card_inter (S ∩ X) (T ∩ X)
    rw [hu, hi] at he
    have hsub : (S ∪ T) ∩ X ⊆ X := Finset.inter_subset_right
    have hlarge : X.card ≤ ((S ∪ T) ∩ X).card := by omega
    have heq : (S ∪ T) ∩ X = X :=
      Finset.eq_of_subset_of_card_le hsub hlarge
    intro a ha
    have ha' : a ∈ (S ∪ T) ∩ X := by
      rw [heq]
      exact ha
    exact (Finset.mem_inter.mp ha').1


theorem star_top_compatibility_verified {α : Type*} [DecidableEq α]
    (k : ℕ) (C U X Y : Finset α)
    (hC : C.card + 1 = k) (hCU : C ⊆ U)
    (hY : Y.card = k) (hCY : C ⊆ Y)
    (hXU : X ⊆ U) (hYout : ¬Y ⊆ U)
    (hXY : k - 1 ≤ (X ∩ Y).card) :
    C ⊆ X := by
  classical
  have hex : ∃ y, y ∈ Y ∧ y ∉ U := by
    by_contra hh
    apply hYout
    intro y hy
    by_contra hn
    exact hh ⟨y, hy, hn⟩
  obtain ⟨y, hyY, hyU⟩ := hex
  have hyC : y ∉ C := fun h => hyU (hCU h)
  have hyX : y ∉ X := fun h => hyU (hXU h)
  have hins : insert y C ⊆ Y := by
    intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · simpa [ha] using hyY
    · exact hCY ha
  have hsize : (insert y C).card = k := by
    simp [hyC, hC]
  have heq : insert y C = Y :=
    Finset.eq_of_subset_of_card_le hins (by omega)
  have hinter : X ∩ Y = X ∩ C := by
    rw [← heq]
    ext a
    simp only [Finset.mem_inter, Finset.mem_insert]
    aesop
  rw [hinter] at hXY
  have hlarge : C.card ≤ (X ∩ C).card := by omega
  have he : X ∩ C = C :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_right hlarge
  intro a ha
  have ha' : a ∈ X ∩ C := by
    rw [he]
    exact ha
  exact (Finset.mem_inter.mp ha').1


theorem independent_star_or_top_verified (r : ℕ)
    (A : Finset (MiddleVertex r))
    (hA : ∀ S ∈ A, ∀ T ∈ A, ¬(middleGraph r).Adj S T)
    (S : MiddleVertex r) (hS : S ∈ A)
    (T : MiddleVertex r) (hT : T ∈ A) (hne : S ≠ T) :
    (∀ X ∈ A, S.1 ∩ T.1 ⊆ X.1) ∨
    (∀ X ∈ A, X.1 ⊆ S.1 ∪ T.1) := by
  classical
  have hp : 0 < 2 ^ r := by positivity
  have hc : (S.1 ∩ T.1).card + 1 = 2 ^ r := by
    have hh := independent_distinct_intersection_verified
      r A hA S hS T hT hne
    omega
  have hloc : ∀ X ∈ A,
      S.1 ∩ T.1 ⊆ X.1 ∨ X.1 ⊆ S.1 ∪ T.1 := by
    intro X hX
    exact nearby_star_or_top_verified (2 ^ r) S.1 T.1 X.1
      X.property hc
      (independent_intersection_verified r A hA S hS X hX)
      (independent_intersection_verified r A hA T hT X hX)
  by_cases hstar : ∀ X ∈ A, S.1 ∩ T.1 ⊆ X.1
  · exact Or.inl hstar
  · right
    push Not at hstar
    obtain ⟨X, hX, hnot⟩ := hstar
    have hXU := (hloc X hX).resolve_left hnot
    intro Y hY
    by_contra hYout
    have hCY := (hloc Y hY).resolve_right hYout
    apply hnot
    apply star_top_compatibility_verified (2 ^ r)
      (S.1 ∩ T.1) (S.1 ∪ T.1) X.1 Y.1
      hc ?_ Y.property hCY hXU hYout
      (independent_intersection_verified r A hA X hX Y hY)
    intro a ha
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp ha).1)


theorem one_more_set_verified {α : Type*} [DecidableEq α]
    (C X : Finset α) (hCX : C ⊆ X)
    (hc : C.card + 1 = X.card) :
    ∃ x, x ∈ X ∧ x ∉ C ∧ X = insert x C := by
  classical
  have hex : ∃ x, x ∈ X ∧ x ∉ C := by
    by_contra hh
    have hsub : X ⊆ C := by
      intro x hx
      by_contra hn
      exact hh ⟨x, hx, hn⟩
    have hh := Finset.card_le_card hsub
    omega
  obtain ⟨x, hxX, hxC⟩ := hex
  have hsub : insert x C ⊆ X := by
    intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · simpa [ha] using hxX
    · exact hCX ha
  have hcard : (insert x C).card = X.card := by
    simp [hxC, hc]
  have he : insert x C = X :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  exact ⟨x, hxX, hxC, he.symm⟩

theorem star_card_bound_verified (r : ℕ)
    (A : Finset (MiddleVertex r))
    (C : Finset (Label (r + 1)))
    (hC : C.card + 1 = 2 ^ r)
    (hA : ∀ X ∈ A, C ⊆ X.1) :
    A.card ≤ 2 ^ r + 1 := by
  classical
  have hm : (A : Set (MiddleVertex r)).MapsTo
      (fun X => X.1) (Cᶜ.image (fun x => insert x C)) := by
    intro X hX
    obtain ⟨x, _, hxC, he⟩ := one_more_set_verified
      C X.1 (hA X hX) (by rw [X.property]; exact hC)
    apply Finset.mem_image.mpr
    exact ⟨x, by simpa using hxC, he.symm⟩
  calc
    A.card ≤ (Cᶜ.image (fun x => insert x C)).card := by
      apply Finset.card_le_card_of_injOn (fun X : MiddleVertex r => X.1) hm
      intro X _ Y _ he
      exact Subtype.ext he
    _ ≤ Cᶜ.card := Finset.card_image_le
    _ = 2 ^ r + 1 := by
      rw [Finset.card_compl]
      have hg : Fintype.card (Label (r + 1)) = 2 * 2 ^ r :=
        groundCard_verified r
      rw [hg]
      omega


theorem top_card_bound_verified (r : ℕ)
    (A : Finset (MiddleVertex r))
    (U : Finset (Label (r + 1)))
    (hU : U.card = 2 ^ r + 1)
    (hA : ∀ X ∈ A, X.1 ⊆ U) :
    A.card ≤ 2 ^ r + 1 := by
  classical
  have hm : (A : Set (MiddleVertex r)).MapsTo
      (fun X => X.1) (U.image (fun x => U.erase x)) := by
    intro X hX
    obtain ⟨x, hxU, hxX, he⟩ := one_more_set_verified
      X.1 U (hA X hX) (by rw [X.property, hU])
    apply Finset.mem_image.mpr
    refine ⟨x, hxU, ?_⟩
    rw [he]
    simp [hxX]
  calc
    A.card ≤ (U.image (fun x => U.erase x)).card := by
      apply Finset.card_le_card_of_injOn (fun X : MiddleVertex r => X.1) hm
      intro X _ Y _ he
      exact Subtype.ext he
    _ ≤ U.card := Finset.card_image_le
    _ = 2 ^ r + 1 := hU

theorem independenceBound_verified (r : ℕ) :
    IndependenceBoundObligation r := by
  classical
  intro A hA
  have hp0 : 0 < 2 ^ r := by positivity
  by_cases hsmall : A.card ≤ 1
  · omega
  · have hex : ∃ S ∈ A, ∃ T ∈ A, S ≠ T := by
      by_contra hh
      have hs : A.card ≤ 1 := Finset.card_le_one.mpr (by
        intro S hS T hT
        by_contra hn
        exact hh ⟨S, hS, T, hT, hn⟩)
      omega
    obtain ⟨S, hS, T, hT, hne⟩ := hex
    have hp : 0 < 2 ^ r := by positivity
    have hc := independent_distinct_intersection_verified
      r A hA S hS T hT hne
    rcases independent_star_or_top_verified r A hA S hS T hT hne
      with hstar | htop
    · apply star_card_bound_verified r A (S.1 ∩ T.1) (by omega) hstar
    · have hU : (S.1 ∪ T.1).card = 2 ^ r + 1 := by
        have he := Finset.card_union_add_card_inter S.1 T.1
        have hs := S.property
        have ht := T.property
        omega
      exact top_card_bound_verified r A (S.1 ∪ T.1) hU htop


theorem chromaticNumber_usedColors_verified (r : ℕ) :
    (middleGraph r).chromaticNumber = ((usedColors r).card : ℕ∞) := by
  classical
  apply le_antisymm
  · let C : (middleGraph r).Coloring (usedColors r) :=
      SimpleGraph.Coloring.mk
        (fun S => ⟨xorColor r S, by simp [usedColors]⟩)
        (by
          intro S T h he
          exact properColor_verified r S T h (congrArg Subtype.val he))
    simpa using C.colorable.chromaticNumber_le
  · apply SimpleGraph.le_chromaticNumber_iff_coloring.mpr
    intro m C
    have hnat : (usedColors r).card ≤ m := by
      let B : Fin m → Finset (MiddleVertex r) :=
        fun c => Finset.univ.filter (fun S => C S = c)
      have hB : ∀ c, (B c).card ≤ 2 ^ r + 1 := by
        intro c
        apply independenceBound_verified r (B c)
        intro S hS T hT hadj
        have hs : C S = c := (Finset.mem_filter.mp hS).2
        have ht : C T = c := (Finset.mem_filter.mp hT).2
        exact C.valid hadj (hs.trans ht.symm)
      have hcount : Fintype.card (MiddleVertex r) ≤ m * (2 ^ r + 1) := by
        calc
          Fintype.card (MiddleVertex r) =
              ∑ c : Fin m, (B c).card := by
            simpa [B] using
              (Finset.sum_card_fiberwise_eq_card_filter
                (Finset.univ : Finset (MiddleVertex r))
                (Finset.univ : Finset (Fin m)) C).symm
          _ ≤ ∑ _c : Fin m, (2 ^ r + 1) := by
            apply Finset.sum_le_sum
            intro c _
            exact hB c
          _ = m * (2 ^ r + 1) := by simp
      rw [colorPartitionCount_verified r] at hcount
      by_contra hn
      have hh : (m + 1) * (2 ^ r + 1) ≤
          (usedColors r).card * (2 ^ r + 1) :=
        Nat.mul_le_mul_right (2 ^ r + 1) (by omega)
      have hp : 0 < 2 ^ r + 1 := by positivity
      rw [Nat.add_mul, Nat.one_mul] at hh
      omega
    exact_mod_cast hnat

theorem mainTheorem_verified (r : ℕ) : MainTheoremObligation r := by
  intro _hr
  rw [chromaticNumber_usedColors_verified, usedColorsCard_verified]


noncomputable def uniformRelabel {α β : Type*}
    (e : α ≃ β) (k : ℕ) :
    UniformSet α k ≃ UniformSet β k :=
  e.finsetCongr.subtypeEquiv (by
    intro S
    change S.card = k ↔ (S.map e.toEmbedding).card = k
    simp)

noncomputable def generalizedKneserRelabel {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (k t : ℕ) :
    generalizedKneser α k t ≃g generalizedKneser β k t where
  toEquiv := uniformRelabel e k
  map_rel_iff' := by
    intro S T
    change
      ((uniformRelabel e k) S ≠ (uniformRelabel e k) T ∧
        ((S.1.map e.toEmbedding) ∩
          (T.1.map e.toEmbedding)).card < t) ↔
      (S ≠ T ∧ (S.1 ∩ T.1).card < t)
    rw [← Finset.map_inter, Finset.card_map]
    constructor
    · rintro ⟨hn, h⟩
      exact ⟨fun he => hn (congrArg (uniformRelabel e k) he), h⟩
    · rintro ⟨hn, h⟩
      exact ⟨fun he => hn ((uniformRelabel e k).injective he), h⟩

theorem conventionalTheorem_verified (r : ℕ) :
    ConventionalTheoremObligation r := by
  intro hr
  let e : Label (r + 1) ≃ Fin (2 * 2 ^ r) :=
    Fintype.equivFinOfCardEq (groundCard_verified r)
  have hi : middleGraph r ≃g
      K (2 * 2 ^ r) (2 ^ r) (2 ^ r - 1) :=
    generalizedKneserRelabel e (2 ^ r) (2 ^ r - 1)
  have hh := SimpleGraph.chromaticNumber_congr hi
  change (K (2 * 2 ^ r) (2 ^ r) (2 ^ r - 1)).chromaticNumber =
    ((Nat.choose (2 * 2 ^ r) (2 ^ r) / (2 ^ r + 1) : ℕ) : ℕ∞)
  rw [← hh]
  exact mainTheorem_verified r hr

end JT913
