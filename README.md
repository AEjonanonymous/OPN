# A Formal Proof of the Non-Existence of Odd Perfect Numbers for Euler Primes p ≥ 5 via Structural Divisibility Constraints.

## 📜 Description

While computational searches have verified the non-existence of odd perfect numbers for all values up to $10^{1500}$, the existence of odd perfect numbers remains one of the oldest unsolved problems in number theory.

This repository presents a **machine-verified proof of the non-existence of such numbers** for the domain $p \ge 5$. By analyzing the abundancy index $I(m^2) = \frac{\sigma(m^2)}{m^2}$, we establish a collision of bounds between the identity-mandated abundancy ceiling and the lower bound forced by the divisibility of the H-factor ($\frac{\sigma(p^k)}{2}$) within the square component $m^2$.

---

## 🏗️ The Proof Structure

According to Euler's theorem, an odd perfect number must take the form:

$$\boxed{N = p^k m^2}$$

Where $p$ is a prime such that $p \equiv k \equiv 1 \pmod 4$.

### 💥 The Collision of Bounds

We demonstrate that for all $p \ge 5$, the minimal prime factors forced into $m^2$ by the Euler prime's structure generate an abundancy that **exceeds the maximum allowable ratio** required by the perfect number identity.

### 🚫 Logical Contradiction

This structural incompatibility creates an **empty set** for the defined domain.

### ✅ Final Verification ($1 \ne 0$)

The logical chain of inequalities was **formally verified using the Lean 4 theorem prover**, confirming that the contradiction is absolute across all $k \ge 1$ and $p \ge 5$.

---

## 💻 Technical Implementation

* **Language:** Lean 4 Web
* **File(s):** `OPN-Proof1.lean` and `OPN-Proof2.lean`
---

Would you like me to draft a `CONTRIBUTING.md` file designed for a mathematics verification project?
