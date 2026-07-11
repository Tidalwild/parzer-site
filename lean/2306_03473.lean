-- Formalized by parZer — CONDITIONAL translation (conditions are the sorry-stubs below). This file recompiles against Mathlib (rev 4049cbf2b80316ac34a98e89e0a8ef55d3a75f55).
-- ── Attribution (CC BY 4.0 / CC0) ─────────────────────────────────────
-- Source paper: “Non-empty pairwise cross-intersecting families”
-- Authors: Yang Huang, Yuejian Peng
-- arXiv: 2306.03473  (https://arxiv.org/abs/2306.03473)
-- License: cc-by
-- Changes: the paper's statements were formalized (translated) into Lean 4 by parZer; proofs are conditional on the sorry-stubs below.
-- ──────────────────────────────────────────────────────────────────────

import Mathlib
set_option autoImplicit false
set_option maxErrors 10000000
set_option maxHeartbeats 1000000
open Real

opaque lexPrec : Finset ℕ → Finset ℕ → Prop
opaque cSeq : ℕ → Finset ℕ → Finset ℕ → Prop
opaque partner : Finset ℕ → Finset ℕ
opaque LFamR : ℕ → ℕ → ℕ → Finset (Finset ℕ)
opaque LFamS : ℕ → Finset ℕ → ℕ → Finset (Finset ℕ)
opaque LInitial : ℕ → ℕ → Finset (Finset ℕ) → Prop
opaque MaximalCrossInt : Finset (Finset ℕ) → Finset (Finset ℕ) → Prop
opaque shadowD : ℕ → Finset (Finset ℕ) → Finset (Finset ℕ)
opaque fFun : ℕ → Finset ℕ → ℚ
opaque alphaF : ℕ → Finset ℕ → Finset ℕ → ℚ
opaque betaF : ℕ → Finset ℕ → Finset ℕ → ℚ
variable (n : ℕ)
variable (t : ℕ)
variable (k : ℕ → ℕ)
variable (d : ℕ → ℚ)
variable (A : ℕ → Finset (Finset ℕ))
variable (m : ℕ → ℕ)
variable (i : ℕ)
def CrossIntersecting (F G : Finset (Finset ℕ)) : Prop := ∀ a ∈ F, ∀ b ∈ G, (a ∩ b).Nonempty
def PairwiseCrossIntersecting (t : ℕ) (A : ℕ → Finset (Finset ℕ)) : Prop :=
  ∀ i ∈ Finset.Icc 1 t, ∀ j ∈ Finset.Icc 1 t, i < j → CrossIntersecting (A i) (A j)
def NonemptyFamilies (t : ℕ) (A : ℕ → Finset (Finset ℕ)) : Prop :=
  ∀ i ∈ Finset.Icc 1 t, (A i).Nonempty
def UniformFamilies (n t : ℕ) (k : ℕ → ℕ) (A : ℕ → Finset (Finset ℕ)) : Prop :=
  ∀ i ∈ Finset.Icc 1 t, A i ⊆ (Finset.Icc 1 n).powersetCard (k i)

/-- custom lemma [external_citation] Kruskal-Katona, \cite{KK1,KK2} (Thm 3) — ASSUMED (stub) -/
theorem lem_kruskal_katona : ∀ (nn kk ll : ℕ) (FA FB : Finset (Finset ℕ)), CrossIntersecting FA FB → CrossIntersecting (LFamR nn FA.card kk) (LFamR nn FB.card ll) := by sorry

/-- custom lemma [external_citation] Frankl-Kupavskii, \cite{FK2018} (Prop 2.11) — ASSUMED (stub) -/
theorem lem_frankl_kupavskii : ∀ (a b nn : ℕ) (P Q : Finset ℕ), a + b ≤ nn → P.Nonempty → Q.Nonempty → P.card ≤ a → Q.card ≤ b → Q = partner P → MaximalCrossInt (LFamS nn P a) (LFamS nn Q b) := by sorry

/-- custom lemma [external_citation] Füredi-Griggs \cite{FG}, Mörs \cite{M} (Prop 2.13) — ASSUMED (stub) -/
theorem lem_furedi_griggs_mors : ∀ (nn kk ll r : ℕ) (FB : Finset (Finset ℕ)), kk + ll < nn → 1 ≤ r → r ≤ ll → FB.card = Nat.choose (nn - r) (ll - r) → (shadowD kk FB).card ≥ Nat.choose (nn - r) kk := by sorry

/-- [proposition] coro7 -/
theorem thm_coro7 (h0 : i ∈ Finset.Icc 1 t) (h1 : ∀ i' ∈ Finset.Icc 1 t, LInitial n (k i') (A i')) (h2 : PairwiseCrossIntersecting t A) (h3 : ∀ j ∈ Finset.erase (Finset.Icc 1 t) i, m i ≤ k j) (h4 : ∃ j ∈ Finset.erase (Finset.Icc 1 t) i, m i = k j) : (A i).card ≤ ∑ s ∈ Finset.Icc 1 (m i), Nat.choose (n - s) (k i - 1) := by sorry

/-- [proposition] coro16 -/
theorem thm_coro16 : ∀ (a b nn : ℕ) (P : Finset ℕ), a + b ≤ nn → P.card ≤ a → CrossIntersecting (LFamS nn (partner P) b) (LFamS nn P a) ∧ MaximalCrossInt (LFamS nn (partner P) b) (LFamS nn P a) ∧ ((LFamS nn (partner P) b).Nonempty ↔ ∃ x ∈ P, x ≤ b) := by sorry

/-- [proposition] clm23 -/
theorem thm_clm23 : ∀ (q : ℕ) (Ri : Finset (Finset ℕ)) (F G : Finset ℕ), F ∈ Ri → G ∈ Ri → lexPrec F G → (∀ x ∈ G, x ≤ q) → q ∈ G → (alphaF i F G = d i ∧ betaF i F G = ∑ j ∈ Finset.erase (Finset.Icc 1 t) i, d j * (Nat.choose (n - q) (k j - (q - k i)) : ℚ)) := by sorry

/-- [lemma] clm3 -/
theorem thm_clm3 (h0 : (∀ j ∈ Finset.erase (Finset.Icc 1 t) i, n = k i + k j) → (∑ j ∈ Finset.erase (Finset.Icc 1 t) i, d j) < d i) : ∀ (c : ℕ) (Ri : Finset (Finset ℕ)) (F G H : Finset ℕ), F ∈ Ri → G ∈ Ri → H ∈ Ri → cSeq c F G → cSeq c G H → (alphaF i F G ≥ betaF i F G → alphaF i G H > betaF i G H) ∧ (fFun i G ≥ fFun i F → fFun i H > fFun i G) := by sorry

/-- [lemma] clm28 -/
theorem thm_clm28 (h0 : (∀ j ∈ Finset.erase (Finset.Icc 1 t) i, n = k i + k j) → (∑ j ∈ Finset.erase (Finset.Icc 1 t) i, d j) < d i) : ∀ (jj c : ℕ) (Rij : Finset (Finset ℕ)) (F G H : Finset ℕ), F ∈ Rij → G ∈ Rij → H ∈ Rij → cSeq c F G → cSeq c G H → (alphaF i F G ≥ betaF i F G → alphaF i G H > betaF i G H) ∧ (fFun i G ≥ fFun i F → fFun i H > fFun i G) := by sorry

/-- [lemma] clm29 -/
theorem thm_clm29 (h0 : (∀ j ∈ Finset.erase (Finset.Icc 1 t) i, n = k i + k j) → (∑ j ∈ Finset.erase (Finset.Icc 1 t) i, d j) < d i) : ∀ (jj : ℕ), 2 ≤ k i → 3 ≤ jj → jj ≤ k i + 1 → (fFun i (Finset.Icc 2 (jj - 1)) ≥ fFun i (Finset.Icc 2 jj) → fFun i (Finset.Icc 2 (jj - 2)) > fFun i (Finset.Icc 2 (jj - 1))) := by sorry

/-- [lemma] clm30 -/
theorem thm_clm30 (h0 : (∀ j ∈ Finset.erase (Finset.Icc 1 t) i, n = k i + k j) → (∑ j ∈ Finset.erase (Finset.Icc 1 t) i, d j) < d i) : ∀ (jj : ℕ), m i + 1 ≤ jj → jj ≤ m i + k i - 1 → (fFun i (Finset.Icc (m i) (jj - 1)) ≥ fFun i (Finset.Icc (m i) jj) → fFun i (Finset.Icc (m i) (jj - 2)) > fFun i (Finset.Icc (m i) (jj - 1))) := by sorry

/-- [claim] claim2.14new -/
theorem thm_claim2_14new : ∀ (kk : ℕ) (R R' : Finset ℕ), 2 ≤ kk → kk ≤ m i → fFun i (Finset.Icc kk (kk + k i - 1)) > fFun i (Insert.insert (kk - 1) (Finset.Icc (n - k i + 2) n)) → lexPrec R R' → fFun i R ≤ fFun i R' := by sorry

/-- [theorem] 2 -/
theorem thm_b_2 (h0 : 2 ≤ t) (h1 : i ∈ Finset.Icc 1 t) (h2 : ∀ i' ∈ Finset.Icc 1 t, 0 < k i') (h3 : ∀ j ∈ Finset.Icc 1 t, 0 < d j) (h4 : Nat.choose (n - 1) (k i - 1) ≤ (A i).card) (h5 : ∀ j ∈ Finset.erase (Finset.Icc 1 t) i, k i + k j ≤ n) (h6 : UniformFamilies n t k A) (h7 : NonemptyFamilies t A) (h8 : PairwiseCrossIntersecting t A) (h9 : ∀ j ∈ Finset.erase (Finset.Icc 1 t) i, m i ≤ k j) (h10 : ∃ j ∈ Finset.erase (Finset.Icc 1 t) i, m i = k j) : (∑ j ∈ Finset.Icc 1 t, d j * ((A j).card : ℚ)) ≤ Max.max (d i * (Nat.choose n (k i) : ℚ) - d i * (Nat.choose (n - m i) (k i) : ℚ) + ∑ j ∈ Finset.erase (Finset.Icc 1 t) i, d j * (Nat.choose (n - m i) (k j - m i) : ℚ)) (∑ j ∈ Finset.Icc 1 t, d j * (Nat.choose (n - 1) (k j - 1) : ℚ)) := by sorry

/-- [theorem] 2+ -/
theorem thm_b_2_2 (h0 : 2 ≤ t) (h1 : ∀ i' ∈ Finset.Icc 1 t, 0 < k i') (h2 : ∀ a ∈ Finset.Icc 1 t, ∀ b ∈ Finset.Icc 1 t, a ≤ b → k b ≤ k a) (h3 : k 1 + k 2 ≤ n) (h4 : ∀ j ∈ Finset.Icc 1 t, 0 < d j) (h5 : UniformFamilies n t k A) (h6 : NonemptyFamilies t A) (h7 : PairwiseCrossIntersecting t A) (h8 : ∀ i' ∈ Finset.Icc 1 t, ∀ j ∈ Finset.erase (Finset.Icc 1 t) i', m i' ≤ k j) (h9 : ∀ i' ∈ Finset.Icc 1 t, ∃ j ∈ Finset.erase (Finset.Icc 1 t) i', m i' = k j) : (∃ i ∈ Finset.Icc 1 t, (∑ j ∈ Finset.Icc 1 t, d j * ((A j).card : ℚ)) ≤ (d i * (Nat.choose n (k i) : ℚ) - d i * (Nat.choose (n - m i) (k i) : ℚ) + ∑ j ∈ Finset.erase (Finset.Icc 1 t) i, d j * (Nat.choose (n - m i) (k j - m i) : ℚ))) ∨ ((∑ j ∈ Finset.Icc 1 t, d j * ((A j).card : ℚ)) ≤ (∑ j ∈ Finset.Icc 1 t, d j * (Nat.choose (n - 1) (k j - 1) : ℚ))) := by
  have h_0 : (∀ i' ∈ Finset.Icc 1 t, (A i').card ≤ Nat.choose (n - 1) (k i' - 1)) → (∑ j ∈ Finset.Icc 1 t, d j * ((A j).card : ℚ)) ≤ (∑ j ∈ Finset.Icc 1 t, d j * (Nat.choose (n - 1) (k j - 1) : ℚ)) := by intro hh; exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (by exact_mod_cast hh j hj) (le_of_lt (h4 j hj)))
  exact (Classical.em (∃ i' ∈ Finset.Icc 1 t, Nat.choose (n - 1) (k i' - 1) ≤ (A i').card)).elim (fun hex => hex.elim (fun i' hip => (le_max_iff.mp (thm_b_2 n t k d A m i' h0 hip.1 h1 h4 hip.2 (fun jj hjj => (le_total i' jj).elim (fun hc => by have hjm : jj ∈ Finset.Icc 1 t := Finset.mem_of_mem_erase hjj; have e1 : k i' ≤ k 1 := h2 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) i' hip.1 (Finset.mem_Icc.mp hip.1).1; have e2 : k jj ≤ k 2 := h2 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) jj hjm (by have hne := Finset.ne_of_mem_erase hjj; have hi1 := (Finset.mem_Icc.mp hip.1).1; omega); omega) (fun hc => by have hjm : jj ∈ Finset.Icc 1 t := Finset.mem_of_mem_erase hjj; have e1 : k i' ≤ k 2 := h2 2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) i' hip.1 (by have hne := Finset.ne_of_mem_erase hjj; have hj1 := (Finset.mem_Icc.mp hjm).1; omega); have e2 : k jj ≤ k 1 := h2 1 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) jj hjm (Finset.mem_Icc.mp hjm).1; omega)) h5 h6 h7 (h8 i' hip.1) (h9 i' hip.1))).imp (fun hl => ⟨i', hip.1, hl⟩) id)) (fun hex => Or.inr (h_0 (fun i' hi' => le_of_lt (not_le.mp (fun hle => hex ⟨i', hi', hle⟩)))))

/-- [proposition] g -/
theorem thm_g_2 (h0 : k 1 + k 2 ≤ n) (h1 : ∀ a ∈ Finset.Icc 1 t, ∀ b ∈ Finset.Icc 1 t, a ≤ b → k b ≤ k a) (h2 : ∀ a ∈ Finset.Icc 1 t, ∀ b ∈ Finset.Icc 1 t, a ≤ b → d b ≤ d a) : ∀ (ss : ℕ), 1 ≤ ss → ss ≤ k t → (∀ jj ∈ Finset.Icc 1 t, fFun jj ({ss} : Finset ℕ) ≤ fFun 1 ({ss} : Finset ℕ)) := by sorry

/-- [theorem] 2++ -/
theorem thm_b_2_3 (h0 : 2 ≤ t) (h1 : ∀ i' ∈ Finset.Icc 1 t, 0 < k i') (h2 : ∀ a ∈ Finset.Icc 1 t, ∀ b ∈ Finset.Icc 1 t, a < b → k b < k a) (h3 : k 1 + k 2 ≤ n) (h4 : ∀ j ∈ Finset.Icc 1 t, 0 < d j) (h5 : ∀ a ∈ Finset.Icc 1 t, ∀ b ∈ Finset.Icc 1 t, a ≤ b → d b ≤ d a) (h6 : UniformFamilies n t k A) (h7 : NonemptyFamilies t A) (h8 : PairwiseCrossIntersecting t A) : (∑ j ∈ Finset.Icc 1 t, d j * ((A j).card : ℚ)) ≤ Max.max (d 1 * (Nat.choose n (k 1) : ℚ) - d 1 * (Nat.choose (n - k t) (k 1) : ℚ) + ∑ j ∈ Finset.erase (Finset.Icc 1 t) 1, d j * (Nat.choose (n - k t) (k j - k t) : ℚ)) (∑ j ∈ Finset.Icc 1 t, d j * (Nat.choose (n - 1) (k j - 1) : ℚ)) := by sorry
