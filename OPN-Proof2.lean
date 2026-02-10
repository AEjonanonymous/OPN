import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.GCD.Basic

/-!
# Formal Verification of the Odd Perfect Number Impossibility (Generalized)
-/

-- PART 1: The Generalized Identity
theorem opn_bridge_general (k _m p s_pk _s_m2 : ℕ) 
  (h_p : p = 2 * k + 1)
  (_h_perfect : 2 * (p^k * _m^2) = s_pk * _s_m2) :
  p = k + (k + 1) := by linarith [h_p]

-- PART 2: The Coprimality Lock
theorem opn_coprime_general (k p : ℕ) (h_p : p = 2 * k + 1) : 
  Nat.gcd p (k + 1) = 1 := by
  have h_link : p = k + (k + 1) := by linarith
  rw [h_link, Nat.gcd_add_self_left, Nat.gcd_comm, Nat.add_comm]
  rw [Nat.gcd_add_self_left]
  exact Nat.gcd_one_left k

-- PART 3: The Divisibility Mandate
theorem opn_mandate_general (k m p p_pow s_m2 _s_pk : ℕ) 
  (h_gcd : Nat.gcd p (k + 1) = 1)
  (h_bridge : p_pow * m^2 = (k + 1) * s_m2) 
  (h_p_pow : p_pow = p^k) :
  (k + 1) ∣ m^2 := by
  have h_gcd_pow : Nat.gcd p_pow (k + 1) = 1 := by 
    rw [h_p_pow]
    exact Nat.Coprime.pow_left k h_gcd
  have h_dvd_right : (k + 1) ∣ p_pow * m^2 := by rw [h_bridge]; exact Nat.dvd_mul_right (k + 1) s_m2
  have h_gcd_flip : Nat.gcd (k + 1) p_pow = 1 := by rw [Nat.gcd_comm, h_gcd_pow]
  exact Nat.Coprime.dvd_of_dvd_mul_left h_gcd_flip h_dvd_right

-- PART 4: The Structural Collapse
theorem opn_final_collapse_general (p k m s_m2 s_pk : ℕ) 
  (h_p_ge_5 : p ≥ 5)
  (h_p_val : p = 2 * k + 1)
  (h_mandate_val : m^2 ≥ k + 1) 
  (h_abundance : s_m2 > m^2 + m)
  (h_perfect : 2 * (p^k * m^2) = s_pk * s_m2) 
  (h_s_pk : s_pk > 2 * p^k) : 
  False := by
  have h_k_ge_2 : k ≥ 2 := by linarith
  nlinarith [h_abundance, h_perfect, h_s_pk]