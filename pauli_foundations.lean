import Mathlib

open Matrix

namespace Pauli

variable {n : ℕ}

/-
Basic facts about Pauli operators, used later in the DLA and Eastin–Knill proofs.
-/

/-
We first define the basic objects that will be use throughout
-/

/- Bitstrings of length n; these index rows/columns of every matrix. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/- A Pauli label v = (x, z). -/
abbrev Label (n : ℕ) := Bits n × Bits n

/- (-1)^k for k ∈ F2. -/
def sgn (k : ZMod 2) : ℂ := (-1) ^ k.val

/- Symplectic form ω(v, w) = x·z' + z·x'. -/
def symp (v w : Label n) : ZMod 2 := v.1 ⬝ᵥ w.2 + v.2 ⬝ᵥ w.1

/- Unphased Pauli: (XZ x z)_{a,b} = (-1)^{z·b} [a = b + x]. -/
def XZ (x z : Bits n) : Matrix (Bits n) (Bits n) ℂ :=
  fun a b => if a = b + x then sgn (z ⬝ᵥ b) else 0

/- Number of Y's, counted in ℕ (NOT in ZMod 2). -/
def ny (v : Label n) : ℕ :=
  (Finset.univ.filter fun j => v.1 j = 1 ∧ v.2 j = 1).card

/- Hermitian Pauli σ_v = i^{ny v} · XZ(x, z). -/
def pauli (v : Label n) : Matrix (Bits n) (Bits n) ℂ :=
  (Complex.I ^ ny v) • XZ v.1 v.2

/-! ## Small lemmas about sgn and 𝔽₂ -/

-- In 𝔽₂ every element is its own negation, so a + a = 0.
lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

-- Pointwise, since each coordinate of a bitstring is in 𝔽₂.
lemma bits_add_self (x : Bits n) : x + x = 0 :=
  funext fun i => zmod2_add_self (x i)

-- (-1)^0 = 1.
lemma sgn_zero_eq : sgn 0 = 1 := by simp [sgn]

-- The representative of 1 in 𝔽₂ is 1, so sgn 1 = -1.
lemma sgn_one_eq : sgn 1 = -1 := by
  unfold sgn
  rw [show (1 : ZMod 2).val = 1 from rfl]
  simp

-- val (a + b) is (val a + val b) mod 2, and (-1)^n depends only on n mod 2.
lemma sgn_add_eq (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  unfold sgn
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

-- sgn a is ±1, so squaring it gives 1.
lemma sgn_mul_self_eq (a : ZMod 2) : sgn a * sgn a = 1 := by
  unfold sgn
  rw [← pow_add, ← two_mul, pow_mul]
  simp

-- Reducing m mod 2 does not change (-1)^m.
lemma sgn_natCast_eq (m : ℕ) : sgn (m : ZMod 2) = (-1) ^ m := by
  unfold sgn
  rw [ZMod.val_natCast, ← neg_one_pow_eq_pow_mod_two]

-- sgn a is real, so it is fixed by conjugation.
lemma sgn_star_eq (a : ZMod 2) : star (sgn a) = sgn a := by
  simp [sgn]

/-! ## P0: helpers -/

-- With x = z = 0 the matrix is diagonal with entries sgn 0 = 1, which is the identity.
theorem XZ_zero : XZ (0 : Bits n) 0 = 1 := by
  ext a b
  simp [XZ, sgn, Matrix.one_apply]

-- On 𝔽₂ the product a * b is 1 exactly when both factors are 1, so the dot product counts Y's mod 2.
theorem ny_parity (v : Label n) : (ny v : ZMod 2) = v.1 ⬝ᵥ v.2 := by
  have key : ∀ a b : ZMod 2, a * b = if a = 1 ∧ b = 1 then 1 else 0 := by decide
  simp only [ny, dotProduct, key, Finset.sum_boole]

-- If z = 0 every term is 1 and there are 2^n of them; otherwise shifting by a coordinate where z is 1 pairs each term with its negative.
theorem char_sum (z : Bits n) :
    ∑ b : Bits n, sgn (z ⬝ᵥ b) = if z = 0 then 2 ^ n else 0 := by
  split_ifs with hz
  · subst hz
    simp [sgn, ZMod.card]
  · obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have hj1 : z j = 1 := by
      revert hj; generalize z j = t; revert t; decide
    have he : z ⬝ᵥ (Pi.single j 1 : Bits n) = 1 := by
      rw [dotProduct_single, hj1, mul_one]
    have hS : (∑ b : Bits n, sgn (z ⬝ᵥ b)) = ∑ b : Bits n, sgn (z ⬝ᵥ (b + Pi.single j 1)) := by
      refine (Fintype.sum_equiv (Equiv.addRight (Pi.single j 1 : Bits n))
        (fun b => sgn (z ⬝ᵥ (b + Pi.single j 1))) (fun b => sgn (z ⬝ᵥ b)) ?_).symm
      intro b
      rw [Equiv.coe_addRight]
    simp only [dotProduct_add, sgn_add_eq, he, sgn_one_eq, mul_neg, mul_one,
      Finset.sum_neg_distrib] at hS
    linear_combination hS / 2

/-! ## P1: master product -/

-- The product sums over an intermediate index, and only c = b + x' is nonzero; that entry contributes the phase sgn (z · x').
theorem XZ_mul (x z x' z' : Bits n) :
    XZ x z * XZ x' z' = sgn (z ⬝ᵥ x') • XZ (x + x') (z + z') := by
  ext a b
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_eq_single (b + x')]
  · simp only [XZ, show b + x' + x = b + (x + x') by abel, if_true]
    split_ifs <;>
      simp only [dotProduct_add, add_dotProduct, sgn_add_eq, mul_zero, zero_mul] <;>
      ring
  · intro c _ hc
    simp [XZ, hc]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## P2: ω is symplectic -/

-- Both the dot product and addition of labels are componentwise, so ω is additive in the first argument.
theorem symp_add_left (u v w : Label n) : symp (u + v) w = symp u w + symp v w := by
  simp only [symp, Prod.fst_add, Prod.snd_add, add_dotProduct]
  ring

-- The two dot products swap when the arguments of ω are swapped.
theorem symp_comm (v w : Label n) : symp v w = symp w v := by
  unfold symp
  rw [dotProduct_comm v.1, dotProduct_comm v.2, add_comm]

-- ω(v, v) is a sum of the form a + a in 𝔽₂.
theorem symp_self (v : Label n) : symp v v = 0 := by
  unfold symp
  rw [dotProduct_comm v.2]
  exact zmod2_add_self _

/-! ## P3: commutation -/

-- XZ_mul gives both products up to a phase, and that phase ratio is sgn (ω(v, w)).
theorem pauli_comm (v w : Label n) :
    pauli v * pauli w = sgn (symp v w) • (pauli w * pauli v) := by
  unfold pauli
  simp only [smul_mul_smul_comm, XZ_mul, smul_smul]
  rw [add_comm w.1, add_comm w.2]
  congr 1
  rw [symp, sgn_add_eq, dotProduct_comm w.2 v.1]
  have := sgn_mul_self_eq (v.1 ⬝ᵥ w.2)
  linear_combination -(Complex.I ^ ny v * Complex.I ^ ny w * sgn (v.2 ⬝ᵥ w.1)) * this

/-! ## P4, P5: Hermitian, involution -/

-- The (a, b) entry of the conjugate transpose is the conjugate of the (b, a) entry, which is the same matrix times sgn (x · z).
lemma XZ_conjTranspose (x z : Bits n) : (XZ x z)ᴴ = sgn (x ⬝ᵥ z) • XZ x z := by
  ext a b
  simp only [Matrix.conjTranspose_apply, XZ, Matrix.smul_apply, smul_eq_mul]
  by_cases h : a = b + x
  · subst h
    rw [if_pos (show b = b + x + x by rw [add_assoc, bits_add_self, add_zero]),
      if_pos rfl, sgn_star_eq, dotProduct_add, sgn_add_eq, dotProduct_comm z x]
    ring
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', add_assoc, bits_add_self, add_zero]))]
    simp

-- Conjugating brings down sgn (x · z) = (-1)^{ny v}, which cancels the conjugation of i^{ny v}.
theorem pauli_hermitian (v : Label n) : (pauli v)ᴴ = pauli v := by
  unfold pauli
  rw [Matrix.conjTranspose_smul, XZ_conjTranspose, smul_smul]
  congr 1
  rw [← ny_parity, sgn_natCast_eq, star_pow, ← mul_pow]
  congr 1
  simp

-- XZ_mul sends the label to 0 and leaves the phase i^{2 ny v} (-1)^{ny v} = 1.
theorem pauli_sq (v : Label n) : pauli v * pauli v = 1 := by
  unfold pauli
  rw [smul_mul_smul_comm, XZ_mul, smul_smul, bits_add_self v.1, bits_add_self v.2,
    XZ_zero]
  have h : Complex.I ^ ny v * Complex.I ^ ny v * sgn (v.2 ⬝ᵥ v.1) = 1 := by
    rw [dotProduct_comm, ← ny_parity, sgn_natCast_eq, ← mul_pow, ← mul_pow,
      Complex.I_mul_I]
    simp
  rw [h, one_smul]

/-! ## P6, P6′: product and bracket -/

-- XZ_mul shows the product is a scalar times σ_{v+w}; when ω(v, w) = 1 the operators anticommute, so that scalar is purely imaginary.
theorem pauli_mul (v w : Label n) :
    ∃ c : ℂ, pauli v * pauli w = c • pauli (v + w) ∧
      (symp v w = 1 → star c = -c) := by
  have hC : Complex.I ^ ny (v + w) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  obtain ⟨c, h1⟩ : ∃ c : ℂ, pauli v * pauli w = c • pauli (v + w) :=
    ⟨Complex.I ^ ny v * Complex.I ^ ny w * sgn (v.2 ⬝ᵥ w.1) * (Complex.I ^ ny (v + w))⁻¹,
      by
        simp only [pauli, smul_mul_smul_comm, XZ_mul, smul_smul, Prod.fst_add,
          Prod.snd_add]
        congr 1
        exact (inv_mul_cancel_right₀ hC _).symm⟩
  refine ⟨c, h1, fun h => ?_⟩
  have key : star c • pauli (v + w) = (-c) • pauli (v + w) := by
    calc star c • pauli (v + w)
        = (c • pauli (v + w))ᴴ := by rw [Matrix.conjTranspose_smul, pauli_hermitian]
      _ = (pauli v * pauli w)ᴴ := by rw [h1]
      _ = pauli w * pauli v := by
          rw [Matrix.conjTranspose_mul, pauli_hermitian, pauli_hermitian]
      _ = -(pauli v * pauli w) := by
          rw [pauli_comm w v, symp_comm, h, sgn_one_eq, neg_one_smul]
      _ = (-c) • pauli (v + w) := by rw [h1, neg_smul]
  have h2 : star c • (1 : Matrix (Bits n) (Bits n) ℂ) = (-c) • 1 := by
    rw [← pauli_sq (v + w), ← Matrix.smul_mul, ← Matrix.smul_mul, key]
  have h3 := congrFun (congrFun h2 0) 0
  simpa using h3

-- The two products agree by pauli_comm, so the commutator is zero.
theorem bracket_zero (u w : Label n) (h : symp u w = 0) :
    ⁅Complex.I • pauli u, Complex.I • pauli w⁆ = 0 := by
  rw [Ring.lie_def, smul_mul_smul_comm, smul_mul_smul_comm, pauli_comm u w, h,
    sgn_zero_eq, one_smul, sub_self]

-- The commutator is 2 i c · (i σ_{u+w}), and c is purely imaginary, so the coefficient is real.
theorem bracket_real (u w : Label n) (h : symp u w = 1) :
    ∃ r : ℝ, ⁅Complex.I • pauli u, Complex.I • pauli w⁆
      = (r : ℂ) • (Complex.I • pauli (u + w)) := by
  obtain ⟨c, hc, hstar⟩ := pauli_mul u w
  have hcc := hstar h
  have hwu : pauli w * pauli u = -(pauli u * pauli w) := by
    rw [pauli_comm w u, symp_comm, h, sgn_one_eq, neg_one_smul]
  have hre : c.re = 0 := by
    have := congrArg Complex.re hcc
    simp at this
    linarith
  have hr : ((2 * Complex.I * c).re : ℂ) = 2 * Complex.I * c := by
    apply Complex.ext <;> simp [hre]
  refine ⟨(2 * Complex.I * c).re, ?_⟩
  rw [hr, Ring.lie_def]
  simp only [smul_mul_smul_comm]
  rw [hwu, hc]
  simp only [smul_neg, sub_neg_eq_add, smul_smul, ← add_smul]
  congr 1
  ring

/-! ## P7: trace -/

-- On the diagonal, x = 0 leaves the character sum; x ≠ 0 makes every diagonal entry zero.
theorem trace_XZ (x z : Bits n) :
    (XZ x z).trace = if x = 0 ∧ z = 0 then 2 ^ n else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [Matrix.trace, XZ, char_sum]
  · simp [Matrix.trace, XZ, hx]

-- If v = w the product is the identity. Otherwise it is a scalar times σ_{v+w} with v + w ≠ 0, whose trace vanishes.
theorem trace_pauli_mul (v w : Label n) :
    (pauli v * pauli w).trace = if v = w then 2 ^ n else 0 := by
  by_cases hvw : v = w
  · subst hvw
    rw [pauli_sq, if_pos rfl, Matrix.trace_one]
    simp [ZMod.card]
  · obtain ⟨c, hc, -⟩ := pauli_mul v w
    have hne : ¬((v + w).1 = 0 ∧ (v + w).2 = 0) := by
      rintro ⟨h1, h2⟩
      apply hvw
      have h0 : v + w = 0 := Prod.ext h1 h2
      have hw : w + w = 0 := Prod.ext (bits_add_self w.1) (bits_add_self w.2)
      calc v = v + (w + w) := by rw [hw, add_zero]
        _ = v + w + w := (add_assoc _ _ _).symm
        _ = w := by rw [h0, zero_add]
    rw [hc, Matrix.trace_smul, if_neg hvw]
    unfold pauli
    rw [Matrix.trace_smul, trace_XZ, if_neg hne]
    simp

/-! ## P8: linear independence -/

-- Right-multiply the dependence relation by σ_w and take the trace; every term drops out except g w.
theorem pauli_linIndep :
    LinearIndependent ℂ (pauli : Label n → Matrix (Bits n) (Bits n) ℂ) := by
  rw [linearIndependent_iff']
  intro s g hsum w hw
  have := congrArg (fun M => Matrix.trace (M * pauli w)) hsum
  simpa [Finset.sum_mul, Matrix.trace_sum, trace_pauli_mul, hw] using this

-- A real dependence among the i σ_v is a complex dependence among the σ_v with coefficients g_i i, so each g_i is zero.
theorem ipauli_linIndep :
    LinearIndependent ℝ (fun v : Label n => Complex.I • pauli v) := by
  rw [linearIndependent_iff']
  intro s g hsum w hw
  have h' : ∑ i ∈ s, ((g i : ℂ) * Complex.I) • pauli i = 0 := by
    calc ∑ i ∈ s, ((g i : ℂ) * Complex.I) • pauli i
        = ∑ i ∈ s, g i • (Complex.I • pauli i) :=
          Finset.sum_congr rfl fun i _ => by ext a b; simp [mul_assoc]
      _ = 0 := hsum
  have := (linearIndependent_iff'.mp pauli_linIndep) s _ h' w hw
  simpa using this

end Pauli
