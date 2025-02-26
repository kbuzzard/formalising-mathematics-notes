import Mathlib.tactic
import Mathlib.Order.OrderIsoNat

/-- The definition of a sequence aₙ in the reals tending to a limit t-/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/-- Definition for a sequence to be strictly monotonically increasing-/
def strict_mono(n: ℕ → ℕ): Prop :=
  ∀ i, n i < n (i+1)

/-- Definition of sequence aₙ having subsequence bₙ-/
def subseq (a: ℕ → ℝ)(b: ℕ → ℝ)(n: ℕ → ℕ) : Prop :=
  strict_mono n ∧ ∀ i, b i = a (n i)

/-- The definition of a sequence being bounded-/
def bd_seq (a : ℕ → ℝ) (M : ℝ) : Prop :=
  ∀ i, |a i| < M

/-- Defines peak points, where in the sequence, all subsequent terms are less-/
def peak_point (a: ℕ → ℝ)(j: ℕ): Prop:=
  ∀ k > j, a k < a j

/-- Used to rewrite peak_point-/
theorem peak_point_def (a : ℕ → ℝ) (j : ℕ) :
    peak_point a j ↔ ∀ k > j, a k < a j :=
  Iff.rfl

/-- The function n for the case S is empty-/
noncomputable def n (a : ℕ → ℝ) (hS : {n | peak_point a n} = ∅) : ℕ → ℕ
| 0 => 1
| k+1 => by
  have hk : ∃ r, r > n a hS k ∧ a (n a hS k) ≤ a r := by
    have hnk : n a hS k ∉ {n | peak_point a n} := Eq.mpr_not (congrFun hS (n a hS k)) fun a ↦ a
    have hjk : ∃ j > (n a hS k), a (n a hS k) ≤ a j := by
      have hpk : ¬ (peak_point a (n a hS k)) := hnk
      rw [peak_point_def] at hpk
      push_neg at hpk
      rcases hpk with ⟨j,hj⟩
      use j
    rcases hjk with ⟨j, ⟨ hj1, hj2⟩⟩
    use j
  exact Exists.choose hk

/-- Proof that the desired elements of n can be produced-/
lemma n_proof {a : ℕ → ℝ} (hS : {n | peak_point a n} = ∅) (k : ℕ) :
    ∃ r, r > n a hS k ∧ a (n a hS k) ≤ a r := by
  have hnk: n a hS k ∉ {n | peak_point a n} := Eq.mpr_not (congrFun hS (n a hS k)) fun a ↦ a
  have hjk: ∃ j > n a hS k, a (n a hS k) ≤ a j := by
    have hpk: ¬ peak_point a (n a hS k) := hnk
    rw [peak_point_def] at hpk
    push_neg at hpk
    rcases hpk with ⟨j,hj⟩
    use j
  rcases hjk with ⟨j, ⟨hj1, hj2⟩⟩
  use j

/--Properties of consecutive terms-/
lemma n_succ_spec {a : ℕ → ℝ} {hS : {n | peak_point a n} = ∅} (k : ℕ) :
    n a hS k < n a hS (k + 1) ∧ a (n a hS k) ≤ a (n a hS (k + 1)) := by
  rw [n]
  exact Exists.choose_spec (n_proof hS k)

/-- The function n for the case S is finite but non-empty -/
noncomputable def n2 (a : ℕ → ℝ) -- (hS: {n | peak_point a n} ≠ ∅)
(hS_fin: {n | peak_point a n}.Finite): ℕ → {n // ∀ s ∈ {n | peak_point a n}, s < n}
| 0 => by
  have hbd:= hS_fin.bddAbove
  use Exists.choose hbd + 1
  have hex: Exists.choose hbd ∈ upperBounds {n | peak_point a n} := Exists.choose_spec hbd
  intro s hs
  rw [mem_upperBounds] at hex
  exact Order.lt_add_one_iff.mpr (hex s hs)
| k + 1 => by
  have hk: ∃ r, r > n2 a hS_fin k ∧ a (n2 a hS_fin k) ≤ a r := by
    have hpk : ¬ (peak_point a (n2 a hS_fin k)) := by
      have hs: ∀ s ∈ {n| peak_point a n}, s < n2 a hS_fin k:= (n2 a hS_fin k).2
      by_contra h
      specialize hs ↑(n2 a hS_fin k) h
      exact (lt_self_iff_false (a ↑(n2 a hS_fin k))).mp (h (↑(n2 a hS_fin k)) hs)
    rw [peak_point_def] at hpk
    push_neg at hpk
    rcases hpk with ⟨r,hr,hr2⟩
    exact ⟨⟨r, fun s hs ↦ Nat.lt_trans (((n2 a hS_fin k).2) s hs) hr⟩,⟨hr, hr2⟩⟩
  exact Exists.choose hk

/-- Proof that the desired elements of n2 can be produced-/
lemma n2_proof {a : ℕ → ℝ}
(hS_fin: {n | peak_point a n}.Finite) (k : ℕ):
  ∃ r, r > n2 a hS_fin k ∧ a (n2 a hS_fin k) ≤ a r := by
  have hpk : ¬ (peak_point a (n2 a hS_fin k)) := by
    have hs: ∀ s ∈ {n| peak_point a n}, s < n2 a hS_fin k:= (n2 a hS_fin k).2
    by_contra h
    specialize hs ↑(n2 a hS_fin k) h
    exact (lt_self_iff_false (a ↑(n2 a hS_fin k))).mp (h (↑(n2 a hS_fin k)) hs)
  rw [peak_point_def] at hpk
  push_neg at hpk
  rcases hpk with ⟨r,hr,hr2⟩
  exact ⟨⟨r, fun s hs ↦ Nat.lt_trans (((n2 a hS_fin k).2) s hs) hr⟩,⟨hr, hr2⟩⟩


/--Properties of consecutive terms-/
lemma n2_succ_spec {a : ℕ → ℝ}
{hS_fin: {n | peak_point a n}.Finite} (k: ℕ):
  n2 a hS_fin k < n2 a hS_fin (k + 1)  ∧ a (n2 a hS_fin k)
  ≤ a (n2 a hS_fin (k + 1)) := by
  rw [n2]
  exact Exists.choose_spec (n2_proof hS_fin k)

/- If a_n is a bounded sequence of real numbers, then it has a convergent subsequence.-/
theorem bolzano_weierstrass {a: ℕ → ℝ}(M: ℝ)(h: 0 < M)(bd: bd_seq a M):
    ∃ b : ℕ → ℝ, ∃ n: ℕ → ℕ , ∃ t, subseq a b n ∧ (TendsTo b t):= by
  -- Consider the set of peak points
  let S := {n | peak_point a n}
  -- The Analysis I notes technically do not consider the case where there are no peak points,
  -- as then there is no maximum.
  -- by_cases hS : S = ∅
  -- · let setb := {a (n a hS i)| i : ℕ}
  --   let t := sSup setb
  --   let b (i : ℕ) : ℝ := a (n a hS i)
  --   use b
  --   use n a hS
  --   use t

  --   constructor
  --   · exact ⟨fun i ↦ (n_succ_spec i).left, fun _ ↦ rfl⟩
  --   · intro ε hε
  --     rw [gt_iff_lt] at hε
  --     have hbd: BddAbove setb := by
  --       refine bddAbove_def.mpr ?_
  --       have hm: ∀ s ∈ setb, s < M := by
  --         rintro s ⟨i, rfl⟩
  --         exact lt_of_abs_lt (bd (n a hS i))
  --       exact ⟨M, fun y a ↦ le_of_lt (hm y a)⟩
  --     have h': setb.Nonempty := Set.nonempty_of_mem (Set.mem_setOf.mpr ⟨0, rfl⟩)

  --     have hexa: ∃ a ∈ setb, sSup setb + -ε < a := Real.add_neg_lt_sSup h' (neg_neg_iff_pos.mpr hε)
  --     rcases hexa with ⟨s, ⟨hs1,hs2⟩⟩
  --     have hexi: ∃ i, a (n a hS i) = s := hs1
  --     rcases hexi with ⟨i , hi⟩
  --     use i
  --     intro k hk
  --     induction k, hk using Nat.le_induction
  --     · simp_rw [b, hi]
  --       have hle0: s - sSup setb ≤ 0 := tsub_nonpos.mpr (le_csSup hbd hs1)
  --       by_cases hP: s - sSup setb = 0
  --       · rwa [hP, abs_zero]
  --       · rw [(abs_of_neg (lt_of_le_of_ne hle0 hP)), neg_sub]
  --         exact sub_lt_comm.mp hs2
  --     · rename_i j _ hbj
  --       have hbjle: a (n a hS (j)) ≤ sSup setb := le_csSup hbd (Set.mem_setOf.mpr ⟨j, rfl⟩)
  --       have hbj1le: a (n a hS (j+1)) ≤ sSup setb := le_csSup hbd (Set.mem_setOf.mpr ⟨j + 1, rfl⟩)
  --       rcases lt_or_eq_of_le hbj1le with hP|hP
  --       · rw [(abs_of_nonpos (tsub_nonpos.mpr hbj1le)), neg_sub]
  --         calc
  --           sSup setb - a (n a hS (j + 1))
  --             ≤ sSup setb - a (n a hS j) := tsub_le_tsub_left ((n_succ_spec j).right) (sSup setb)
  --           _ < ε := by
  --             have habsbj: |a (n a hS (j)) - sSup setb| = -(a (n a hS (j)) - sSup setb) := by
  --               rcases lt_or_eq_of_le hbjle with hP2|hP2
  --               · exact abs_of_nonpos (tsub_nonpos.mpr hbjle)
  --               · rw [hP2, sub_self, abs_zero, neg_zero]
  --             rwa [habsbj, neg_sub] at hbj
  --       · simpa [b, hP, t]

-- Now we split into the finite case and the infinite case
  · rcases Set.finite_or_infinite S with hS_fin | hS_inf

    · let setb := {a (n2 a hS_fin i)| i : ℕ}
      let t := sSup setb
      let b: ℕ → ℝ
      | i => a (n2 a hS_fin i)
      use b
      use (fun i ↦ n2 a hS_fin i)
      use t

      refine ⟨⟨fun i ↦(n2_succ_spec i).left,fun _ ↦ rfl⟩,?_⟩
      intro ε hε
      rw [gt_iff_lt] at hε
      have hbd: BddAbove setb := by
        refine bddAbove_def.mpr ?_
        have hm: ∀ s ∈ setb, s < M := by
          rintro s ⟨i, rfl⟩
          exact lt_of_abs_lt (bd (n2 a hS_fin i))
        exact ⟨M, fun y a ↦ le_of_lt (hm y a)⟩
      -- Shows non-emptiness by providing n(0)
      have h': setb.Nonempty := Set.nonempty_of_mem (Set.mem_setOf.mpr ⟨0, rfl⟩)
      -- Property of the supremum that we can pick some element less than epsilon from it
      have hexa: ∃ a ∈ setb, sSup setb + -ε < a :=
      Real.add_neg_lt_sSup h' (neg_neg_iff_pos.mpr hε)
      rcases hexa with ⟨s, ⟨hs1,hs2⟩⟩
      have hexi:= hs1
      rcases hexi with ⟨i , hi⟩
      use i

      intro k hk
      induction k, hk using Nat.le_induction
      · simp_rw [b, hi]
        have hle0: s - sSup setb ≤ 0 := tsub_nonpos.mpr (le_csSup hbd hs1)
        by_cases hP: s - sSup setb = 0
        · rwa [hP, abs_zero]
        · rw [(abs_of_neg (lt_of_le_of_ne hle0 hP)), neg_sub]
          exact sub_lt_comm.mp hs2
      · rename_i j _ hbj
        have hbjle: a (n2 a hS_fin j) ≤ sSup setb := le_csSup hbd (Set.mem_setOf.mpr ⟨j, rfl⟩)
        have hbj1le: a (n2 a hS_fin (j+1)) ≤ sSup setb :=
        le_csSup hbd (Set.mem_setOf.mpr ⟨j + 1, rfl⟩)
        rcases lt_or_eq_of_le hbj1le with hP|hP
        · rw [(abs_of_nonpos (tsub_nonpos.mpr hbj1le)), neg_sub]
          calc
          -- subsequent terms of the subsequence decrease
          sSup setb - a (n2 a hS_fin (j + 1))
            ≤ sSup setb - a (n2 a hS_fin j) :=
              tsub_le_tsub_left ((n2_succ_spec j).right) (sSup setb)
          _ < ε := by
            have habsbj: |a (n2 a hS_fin (j)) - sSup setb| =
            -(a (n2 a hS_fin j) - sSup setb) := by
              rcases lt_or_eq_of_le hbjle with hP2|hP2
              · exact abs_of_nonpos (tsub_nonpos.mpr hbjle)
              · rw [hP2, sub_self, abs_zero, neg_zero]
            rwa [habsbj, neg_sub] at hbj
        · simpa [b, hP, t]

    · have : Infinite S := Set.infinite_coe_iff.mpr hS_inf
      let n := Nat.Subtype.orderIsoOfNat S
      let b : ℕ → ℝ
        | i => a (n i)
      let setb := {b i | i : ℕ}
      let t := sInf setb
      use b
      use (fun i ↦ n i)
      use t

      constructor
      · constructor
        · intro i
          simp
        · exact fun _ ↦ rfl
      · intro ε hε
        rw [gt_iff_lt] at hε

        have hbd: BddBelow setb := by
          use -M
          intro s hs
          rcases hs with ⟨i,hi⟩
          specialize bd (n i)
          have hltM: |s| < M := lt_of_eq_of_lt (congrArg abs (id (Eq.symm hi))) bd
          exact le_of_lt (abs_lt.mp hltM).1

        have h': setb.Nonempty := Set.nonempty_of_mem (Set.mem_setOf.mpr ⟨0, rfl⟩)
        rcases (Real.lt_sInf_add_pos h' hε) with ⟨s, ⟨hs1,hs2⟩⟩
        have hexi: ∃ i, b i = s := hs1
        rcases hexi with ⟨i , hi⟩

        use i
        intro k hk
        have hani: peak_point a (n i) := (n i).prop
        rcases lt_or_eq_of_le hk with hP | hP

        · specialize hani (n k) (OrderIso.GCongr.orderIso_apply_lt_apply n hP)
          have hlebk : sInf setb ≤ b k := csInf_le hbd ⟨k, rfl⟩
          rcases lt_or_eq_of_le hlebk with hP2 | hP2
          · rw [abs_of_pos (sub_pos.mpr hP2)]
            linarith
          · rw [← hP2]
            simpa
        · rw [← hP, hi]
          have hinfle:= csInf_le hbd hs1
          have habs: |s-t| = s-t := by
            rcases lt_or_eq_of_le hinfle with hP2 | hP2
            · exact abs_of_pos (sub_pos.mpr hP2)
            · simpa
          rw [habs]
          exact (tsub_lt_iff_left hinfle).mpr hs2
