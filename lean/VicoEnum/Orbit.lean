/-
  VicoEnum/Orbit.lean

  Orbit counting for the divisibility statements.

  Three results in the paper divide the count by the size of a group: `5 ∣ T(N,5)` from the
  free rotation action (Theorem `thm:free`), `10 ∣ T(p,5)` from that together with the
  reversal involution (Proposition `prop:tenprime`), and the orbit split of Theorem
  `thm:orbit`. Each needs the same two facts, stated here once for an arbitrary finite set
  carrying a map, with no `MulAction` instance required:

    * a fixed-point-free map of order `5` forces `5 ∣ card`;
    * an involution makes `card` congruent to its number of fixed points mod `2`.

  Both are proved by induction on the cardinality, removing one orbit at a time.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace VicoEnum

open Finset

/-! ## A fixed-point-free map of order five -/

section OrderFive

variable {α : Type*} [DecidableEq α] {f : α → α}

/-- A map with `f⁵ = id` is injective. -/
theorem inj_of_order_five (hord : ∀ x, f (f (f (f (f x)))) = x) : Function.Injective f := by
  intro a b hab
  have : f (f (f (f (f a)))) = f (f (f (f (f b)))) := by rw [hab]
  rwa [hord, hord] at this

/-- If `f⁵ = id` and `f` has no fixed point at `x`, then neither do `f²`, `f³`, `f⁴`. -/
theorem no_fixed_iterate (hord : ∀ x, f (f (f (f (f x)))) = x) {x : α} (hx : f x ≠ x) :
    f (f x) ≠ x ∧ f (f (f x)) ≠ x ∧ f (f (f (f x))) ≠ x := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have key := hord x
    rw [h, h] at key
    exact hx key
  · intro h
    have key := hord x
    -- f⁵x = f²(f³x) = f²x, and f³x = x gives f²x = f⁵x = x, then f x = f(f³ x) ... reduce
    have h5 : f (f x) = x := by
      have : f (f (f (f (f x)))) = f (f x) := by rw [h]
      rw [key] at this; exact this.symm
    have key2 := hord x
    rw [h5, h5] at key2
    exact hx key2
  · intro h
    have key := hord x
    rw [h] at key
    exact hx key

/-- The orbit of `x`. -/
def orb (f : α → α) (x : α) : Finset α := {x, f x, f (f x), f (f (f x)), f (f (f (f x)))}

theorem card_orb (hord : ∀ x, f (f (f (f (f x)))) = x) {x : α} (hx : f x ≠ x) :
    (orb f x).card = 5 := by
  obtain ⟨h2, h3, h4⟩ := no_fixed_iterate hord hx
  have hinj := inj_of_order_five hord
  have d01 : x ≠ f x := fun h => hx h.symm
  have d02 : x ≠ f (f x) := fun h => h2 h.symm
  have d03 : x ≠ f (f (f x)) := fun h => h3 h.symm
  have d04 : x ≠ f (f (f (f x))) := fun h => h4 h.symm
  have d12 : f x ≠ f (f x) := fun h => d01 (hinj h)
  have d13 : f x ≠ f (f (f x)) := fun h => d02 (hinj h)
  have d14 : f x ≠ f (f (f (f x))) := fun h => d03 (hinj h)
  have d23 : f (f x) ≠ f (f (f x)) := fun h => d12 (hinj h)
  have d24 : f (f x) ≠ f (f (f (f x))) := fun h => d13 (hinj h)
  have d34 : f (f (f x)) ≠ f (f (f (f x))) := fun h => d23 (hinj h)
  simp only [orb]
  rw [card_insert_of_not_mem (by simp [d01, d02, d03, d04]),
    card_insert_of_not_mem (by simp [d12, d13, d14]),
    card_insert_of_not_mem (by simp [d23, d24]),
    card_insert_of_not_mem (by simp [d34]),
    card_singleton]

theorem orb_mem_self {x : α} : x ∈ orb f x := by simp [orb]

theorem orb_subset {s : Finset α} (hmap : ∀ y ∈ s, f y ∈ s) {x : α} (hx : x ∈ s) :
    orb f x ⊆ s := by
  intro y hy
  simp only [orb, mem_insert, mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact hx
  · exact hmap _ hx
  · exact hmap _ (hmap _ hx)
  · exact hmap _ (hmap _ (hmap _ hx))
  · exact hmap _ (hmap _ (hmap _ (hmap _ hx)))

theorem orb_invariant (hord : ∀ x, f (f (f (f (f x)))) = x) {x y : α} (hy : y ∈ orb f x) :
    f y ∈ orb f x := by
  simp only [orb, mem_insert, mem_singleton] at hy ⊢
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · exact Or.inl (hord x)

/-- Membership in an orbit is symmetric for a map of order five. -/
theorem orb_symm (hord : ∀ x, f (f (f (f (f x)))) = x) {x y : α} (hy : y ∈ orb f x) :
    x ∈ orb f y := by
  simp only [orb, mem_insert, mem_singleton] at hy ⊢
  rcases hy with rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inr (Or.inr (Or.inr (hord x).symm)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl (hord x).symm)))
      | exact Or.inr (Or.inr (Or.inl (hord x).symm))
      | exact Or.inr (Or.inl (hord x).symm)

/-- **A fixed-point-free map of order five divides the count by five.** -/
theorem five_dvd_card_of_free (hord : ∀ x, f (f (f (f (f x)))) = x) :
    ∀ (s : Finset α), (∀ x ∈ s, f x ∈ s) → (∀ x ∈ s, f x ≠ x) → 5 ∣ s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hmap hfree
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hsub : orb f x ⊆ s := orb_subset hmap hx
      have hcard : (orb f x).card = 5 := card_orb hord (hfree x hx)
      have hlt : s \ orb f x ⊂ s := by
        refine Finset.sdiff_ssubset hsub ?_
        exact ⟨x, orb_mem_self⟩
      have hmap' : ∀ y ∈ s \ orb f x, f y ∈ s \ orb f x := by
        intro y hy
        rw [mem_sdiff] at hy ⊢
        refine ⟨hmap y hy.1, fun hcon => hy.2 ?_⟩
        -- if f y ∈ orb, then y ∈ orb, since orb is f-invariant and f is injective on it
        have hinj := inj_of_order_five hord
        simp only [orb, mem_insert, mem_singleton] at hcon ⊢
        rcases hcon with h | h | h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (hinj (by rw [h, hord])))))
        · exact Or.inl (hinj h)
        · exact Or.inr (Or.inl (hinj h))
        · exact Or.inr (Or.inr (Or.inl (hinj h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hinj h))))
      have hfree' : ∀ y ∈ s \ orb f x, f y ≠ y := fun y hy => hfree y (mem_sdiff.mp hy).1
      have hrec := ih _ hlt hmap' hfree'
      have hsplit : s.card = (s \ orb f x).card + 5 := by
        rw [Finset.card_sdiff hsub, hcard]
        have : (orb f x).card ≤ s.card := Finset.card_le_card hsub
        omega
      omega

/-! ## Counting a property across orbits

`five_dvd_card_of_free` peels one orbit at a time off a finite set. The same induction counts
a predicate: if every orbit meets `P` in exactly `c` points, then `5 |s.filter P| = c |s|`,
since the count is `cR` and the size is `5R`. Stating it multiplied through by `5` avoids
division and the need to name `R`. -/

/-- **Uniform orbit count.** If every orbit inside `s` contains exactly `c` points of `P`,
then `5 |s.filter P| = c |s|`. -/
theorem orbit_count_uniform (hord : ∀ x, f (f (f (f (f x)))) = x)
    (P : α → Prop) [DecidablePred P] (c : ℕ) :
    ∀ (s : Finset α), (∀ x ∈ s, f x ∈ s) → (∀ x ∈ s, f x ≠ x) →
      (∀ x ∈ s, ((orb f x).filter P).card = c) →
      5 * (s.filter P).card = c * s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hmap hfree hcnt
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hsub : orb f x ⊆ s := orb_subset hmap hx
      have hcard : (orb f x).card = 5 := card_orb hord (hfree x hx)
      have hlt : s \ orb f x ⊂ s := Finset.sdiff_ssubset hsub ⟨x, orb_mem_self⟩
      have hmap' : ∀ y ∈ s \ orb f x, f y ∈ s \ orb f x := by
        intro y hy
        rw [mem_sdiff] at hy ⊢
        refine ⟨hmap y hy.1, fun hcon => hy.2 ?_⟩
        have hinj := inj_of_order_five hord
        simp only [orb, mem_insert, mem_singleton] at hcon ⊢
        rcases hcon with h | h | h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (hinj (by rw [h, hord])))))
        · exact Or.inl (hinj h)
        · exact Or.inr (Or.inl (hinj h))
        · exact Or.inr (Or.inr (Or.inl (hinj h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hinj h))))
      have hfree' : ∀ y ∈ s \ orb f x, f y ≠ y := fun y hy => hfree y (mem_sdiff.mp hy).1
      have hcnt' : ∀ y ∈ s \ orb f x, ((orb f y).filter P).card = c :=
        fun y hy => hcnt y (mem_sdiff.mp hy).1
      have hrec := ih _ hlt hmap' hfree' hcnt'
      -- the filtered count splits the same way as the raw count
      have hfsplit : (s.filter P).card
          = ((s \ orb f x).filter P).card + ((orb f x).filter P).card := by
        rw [← Finset.card_union_of_disjoint (by
          refine Finset.disjoint_filter_filter ?_
          exact Finset.sdiff_disjoint)]
        congr 1
        ext y
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨hy, hP⟩
          by_cases horb : y ∈ orb f x
          · exact Or.inr ⟨horb, hP⟩
          · exact Or.inl ⟨⟨hy, horb⟩, hP⟩
        · rintro (⟨⟨hy, -⟩, hP⟩ | ⟨hy, hP⟩)
          · exact ⟨hy, hP⟩
          · exact ⟨hsub hy, hP⟩
      have hsplit : s.card = (s \ orb f x).card + 5 := by
        rw [Finset.card_sdiff hsub, hcard]
        have : (orb f x).card ≤ s.card := Finset.card_le_card hsub
        omega
      rw [hfsplit, hcnt x hx, hsplit, Nat.mul_add, Nat.mul_add, hrec]
      ring

/-- **One exceptional orbit.** If every orbit except the one through `e` meets `P` in `c`
points, and that one meets it in `c'`, then `5 |s.filter P| = c (|s| - 5) + 5 c'`. This is the
shape `thm:orbit` needs: `c = 2` on the ordinary orbits and `c' = 5` on the Conway--Coxeter
orbit. -/
theorem orbit_count_one_exception (hord : ∀ x, f (f (f (f (f x)))) = x)
    (P : α → Prop) [DecidablePred P] (c c' : ℕ) (s : Finset α) (e : α) (he : e ∈ s)
    (hmap : ∀ x ∈ s, f x ∈ s) (hfree : ∀ x ∈ s, f x ≠ x)
    (hcnt : ∀ x ∈ s \ orb f e, ((orb f x).filter P).card = c)
    (hexc : ((orb f e).filter P).card = c') :
    5 * (s.filter P).card = c * (s.card - 5) + 5 * c' := by
  have hsub : orb f e ⊆ s := orb_subset hmap he
  have hcard : (orb f e).card = 5 := card_orb hord (hfree e he)
  have hmap' : ∀ y ∈ s \ orb f e, f y ∈ s \ orb f e := by
    intro y hy
    rw [mem_sdiff] at hy ⊢
    refine ⟨hmap y hy.1, fun hcon => hy.2 ?_⟩
    have hinj := inj_of_order_five hord
    simp only [orb, mem_insert, mem_singleton] at hcon ⊢
    rcases hcon with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hinj (by rw [h, hord])))))
    · exact Or.inl (hinj h)
    · exact Or.inr (Or.inl (hinj h))
    · exact Or.inr (Or.inr (Or.inl (hinj h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hinj h))))
  have hfree' : ∀ y ∈ s \ orb f e, f y ≠ y := fun y hy => hfree y (mem_sdiff.mp hy).1
  have hrec := orbit_count_uniform hord P c _ hmap' hfree' hcnt
  -- the two splittings, of the filtered count and of the raw count
  have hfsplit : (s.filter P).card
      = ((s \ orb f e).filter P).card + ((orb f e).filter P).card := by
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter Finset.sdiff_disjoint)]
    congr 1
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hy, hP⟩
      by_cases horb : y ∈ orb f e
      · exact Or.inr ⟨horb, hP⟩
      · exact Or.inl ⟨⟨hy, horb⟩, hP⟩
    · rintro (⟨⟨hy, -⟩, hP⟩ | ⟨hy, hP⟩)
      · exact ⟨hy, hP⟩
      · exact ⟨hsub hy, hP⟩
  have hsplit : (s \ orb f e).card = s.card - 5 := by
    rw [Finset.card_sdiff hsub, hcard]
  rw [hfsplit, hexc, Nat.mul_add, hrec, hsplit]

/-! ## Indexing an orbit by `ZMod 5`

`orbit_split` states its conclusion as a count over `j : ZMod 5`; the counting lemmas above
want a count over `orb f x`. The map `j ↦ f^[j.val] x` carries one to the other. It lands in
the orbit and hits all of it, so its image is exactly `orb f x`, of size five by `card_orb`;
since `ZMod 5` also has five elements, the map is injective and the two counts agree. -/

/-- The five iterates, indexed by `ZMod 5`. -/
def orbIdx (f : α → α) (x : α) (j : ZMod 5) : α := f^[j.val] x

theorem orbIdx_zero (f : α → α) (x : α) : orbIdx f x 0 = x := rfl
theorem orbIdx_one (f : α → α) (x : α) : orbIdx f x 1 = f x := rfl
theorem orbIdx_two (f : α → α) (x : α) : orbIdx f x 2 = f (f x) := rfl
theorem orbIdx_three (f : α → α) (x : α) : orbIdx f x 3 = f (f (f x)) := rfl
theorem orbIdx_four (f : α → α) (x : α) : orbIdx f x 4 = f (f (f (f x))) := rfl

/-- The image of `orbIdx` is exactly the orbit. -/
theorem image_orbIdx (f : α → α) (x : α) :
    (Finset.univ : Finset (ZMod 5)).image (orbIdx f x) = orb f x := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, orb, mem_insert, mem_singleton]
  constructor
  · rintro ⟨j, rfl⟩
    have hj : j.val < 5 := j.val_lt
    interval_cases h : j.val <;>
      simp only [orbIdx, h, Function.iterate_zero_apply, Function.iterate_one] <;> tauto
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

/-- **The orbit count equals the count over `ZMod 5`.** -/
theorem orbIdx_mem_orb (f : α → α) (x : α) (j : ZMod 5) : orbIdx f x j ∈ orb f x := by
  have h : j.val < 5 := j.val_lt
  simp only [orbIdx, orb, mem_insert, mem_singleton]
  interval_cases hj : (j.val) <;> simp [Function.iterate_succ_apply]

theorem orb_filter_card (hord : ∀ y, f (f (f (f (f y)))) = y) {x : α} (hx : f x ≠ x)
    (P : α → Prop) [DecidablePred P] :
    ((orb f x).filter P).card
      = (Finset.univ.filter (fun j : ZMod 5 => P (orbIdx f x j))).card := by
  classical
  have hinj : Set.InjOn (orbIdx f x) (Finset.univ : Finset (ZMod 5)) := by
    rw [← Finset.card_image_iff, image_orbIdx, card_orb hord hx]
    simp
  refine (Finset.card_bij (fun j _ => orbIdx f x j) ?_ ?_ ?_).symm
  · intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    refine ⟨?_, hj.2⟩
    rw [← image_orbIdx f x]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  · intro a _ b _ hab
    exact hinj (Finset.mem_univ a) (Finset.mem_univ b) hab
  · intro y hy
    simp only [Finset.mem_filter] at hy
    obtain ⟨hmem, hP⟩ := hy
    rw [← image_orbIdx f x] at hmem
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    exact ⟨j, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj]; exact hP, hj⟩

end OrderFive

/-! ## An involution -/

section Involution

variable {α : Type*} [DecidableEq α] {g : α → α}

/-- **An involution makes the count congruent to its fixed points mod two.** -/
theorem card_add_fixed_even (hinv : ∀ x, g (g x) = x) :
    ∀ (s : Finset α), (∀ x ∈ s, g x ∈ s) →
      (s.card + (s.filter (fun x => g x = x)).card) % 2 = 0 := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hmap
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    by_cases hfix : g x = x
    · -- remove the fixed point x
      have hlt : s.erase x ⊂ s := Finset.erase_ssubset hx
      have hmap' : ∀ y ∈ s.erase x, g y ∈ s.erase x := by
        intro y hy
        rw [mem_erase] at hy ⊢
        refine ⟨fun hcon => hy.1 ?_, hmap y hy.2⟩
        rw [← hinv y, hcon, hfix]
      have hrec := ih _ hlt hmap'
      have h1 : s.card = (s.erase x).card + 1 := by
        rw [Finset.card_erase_of_mem hx]
        have := Finset.card_pos.mpr ⟨x, hx⟩; omega
      have hmem : x ∈ s.filter (fun y => g y = y) := Finset.mem_filter.mpr ⟨hx, hfix⟩
      have he : (s.erase x).filter (fun y => g y = y)
          = (s.filter (fun y => g y = y)).erase x := by
        ext y; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
      have h2 : (s.filter (fun y => g y = y)).card
          = ((s.erase x).filter (fun y => g y = y)).card + 1 := by
        rw [he, Finset.card_erase_of_mem hmem]
        have := Finset.card_pos.mpr ⟨x, hmem⟩; omega
      omega
    · -- remove the two-element orbit {x, g x}
      have hgx : g x ∈ s := hmap x hx
      have hpair : ({x, g x} : Finset α).card = 2 := by
        rw [Finset.card_insert_of_not_mem (by simpa using fun h => hfix h.symm),
          Finset.card_singleton]
      have hsub : ({x, g x} : Finset α) ⊆ s := by
        intro y hy; simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact hx
        · exact hgx
      have hlt : s \ {x, g x} ⊂ s := Finset.sdiff_ssubset hsub ⟨x, by simp⟩
      have hmap' : ∀ y ∈ s \ ({x, g x} : Finset α), g y ∈ s \ ({x, g x} : Finset α) := by
        intro y hy
        rw [mem_sdiff] at hy ⊢
        refine ⟨hmap y hy.1, fun hcon => hy.2 ?_⟩
        simp only [mem_insert, mem_singleton] at hcon ⊢
        rcases hcon with h | h
        · exact Or.inr (by rw [← hinv y, h])
        · exact Or.inl (by have := hinv x; rw [← hinv y, h, this])
      have hrec := ih _ hlt hmap'
      have hc : s.card = (s \ ({x, g x} : Finset α)).card + 2 := by
        rw [Finset.card_sdiff hsub, hpair]
        have := Finset.card_le_card hsub; rw [hpair] at this; omega
      have hfeq : (s \ ({x, g x} : Finset α)).filter (fun y => g y = y)
          = s.filter (fun y => g y = y) := by
        ext y
        simp only [Finset.mem_filter, mem_sdiff, mem_insert, mem_singleton]
        constructor
        · rintro ⟨⟨hy, -⟩, hp⟩; exact ⟨hy, hp⟩
        · rintro ⟨hy, hp⟩
          refine ⟨⟨hy, ?_⟩, hp⟩
          rintro (rfl | rfl)
          · exact hfix hp
          · exact hfix (((hinv x).symm.trans hp).symm)
      have hf : (s.filter (fun y => g y = y)).card
          = ((s \ ({x, g x} : Finset α)).filter (fun y => g y = y)).card := by rw [hfeq]
      omega

end Involution

end VicoEnum
