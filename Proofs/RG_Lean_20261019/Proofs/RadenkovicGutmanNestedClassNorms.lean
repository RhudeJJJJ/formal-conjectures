/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedClassPolynomials

namespace Gebendorfer.RadenkovicGutman.NestedClassNorms
open NestedArithmetic NestedClassPolynomials ClassNormPolynomials
noncomputable section
set_option maxHeartbeats 0

theorem complexValue_add (a b : CP) (x : Fin 3 → ℝ) :
    complexValue (cadd a b) x=complexValue a x+complexValue b x := by
  rfl

theorem complexValue_sub (a b : CP) (x : Fin 3 → ℝ) :
    complexValue (csub a b) x=complexValue a x-complexValue b x := by
  apply Complex.ext <;> dsimp [complexValue,csub,NestedClassPolynomials.sub,value] <;> ring

theorem complexValue_mul (a b : CP) (x : Fin 3 → ℝ) :
    complexValue (cmul a b) x=complexValue a x*complexValue b x := by
  apply Complex.ext <;> simp [complexValue,cmul,NestedClassPolynomials.add,
    NestedClassPolynomials.sub,NestedClassPolynomials.mul,value,
    Complex.mul_re,Complex.mul_im,sub_eq_add_neg]

theorem complexValue_star (a : CP) (x : Fin 3 → ℝ) :
    complexValue (cstar a) x=star (complexValue a x) := by
  apply Complex.ext <;> simp [complexValue,cstar,rat,NestedClassPolynomials.mul,value]

theorem normValue (a : CP) (x : Fin 3 → ℝ) :
    value (cnorm a) x=Complex.normSq (complexValue a x) := by
  simp [cnorm,NestedClassPolynomials.add,NestedClassPolynomials.pow,value,
    complexValue,Complex.normSq_apply,pow_two]

theorem normSq_scaled (l : ℝ) (z : ℂ) :
    Complex.normSq ((l : ℂ)*z)=l^2*Complex.normSq z := by
  simp [Complex.normSq_apply,pow_two]
  ring

theorem common_positive (c₁ c₂ : Fin 5) (x : Fin 3 → ℝ) (hx : 0 < x 0) :
    0 < value (common c₁ c₂) x := by
  change 0 < value (armDen c₁) x*value (armDen c₂) x
  rw [armDen_sound,armDen_sound]
  exact mul_pos (ArmRationalForm.denominator_positive c₁ (x 0) hx)
    (ArmRationalForm.denominator_positive c₂ (x 0) hx)

/-- The common arm denominators occur to the same fourth power in all
three norm expressions. No identification by numerical values is used. -/
theorem programs_sound (d : ℚ) (c₁ c₂ : Fin 5) (x : Fin 3 → ℝ) (hx : 0 < x 0) :
    let l := value (common c₁ c₂) x
    let p := ArmClasses.parameter (x 0) c₁ (x 1)
    let q := ArmClasses.parameter (x 0) c₂ (x 2)
    value (programU d c₁ c₂) x=l^4*U d (x 0) p q ∧
    value (programV d c₁ c₂) x=l^4*V d (x 0) p q ∧
    value (programJ d c₁ c₂) x=l^4*J d (x 0) p q := by
  obtain ⟨ha,hb,hc,he⟩ := coefficients_sound d c₁ c₂ x hx
  let l := value (common c₁ c₂) x
  let p := ArmClasses.parameter (x 0) c₁ (x 1)
  let q := ArmClasses.parameter (x 0) c₂ (x 2)
  have hu : U d (x 0) p q=Complex.normSq
      (polyB d (x 0) p q*star (polyE d (x 0) p q)-polyA d p q*star (polyC d (x 0) p q)) := by
    simp [U,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    ring
  have hv : V d (x 0) p q=Complex.normSq
      (polyA d p q*polyE d (x 0) p q-polyB d (x 0) p q*polyC d (x 0) p q) := by
    simp [V,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    ring
  have hj : J d (x 0) p q=(Complex.normSq (polyB d (x 0) p q)-Complex.normSq (polyA d p q))^2 := by
    simp [J,Complex.normSq_apply]
    ring
  have hscale (z : ℂ) : Complex.normSq ((l : ℂ)^2*z)=l^4*Complex.normSq z := by
    have heq : (l : ℂ)^2*z=(l : ℂ)*((l : ℂ)*z) := by ring
    rw [heq,normSq_scaled,normSq_scaled]
    ring
  change value (programU d c₁ c₂) x=l^4*U d (x 0) p q ∧
    value (programV d c₁ c₂) x=l^4*V d (x 0) p q ∧
    value (programJ d c₁ c₂) x=l^4*J d (x 0) p q
  constructor
  · rw [hu]
    simp only [programU,normValue,complexValue_sub,complexValue_mul,complexValue_star,
      ha,hb,hc,he]
    have heq : ((l : ℂ)*polyB d (x 0) p q)*star ((l : ℂ)*polyE d (x 0) p q)-
        ((l : ℂ)*polyA d p q)*star ((l : ℂ)*polyC d (x 0) p q)=
        (l : ℂ)^2*(polyB d (x 0) p q*star (polyE d (x 0) p q)-
          polyA d p q*star (polyC d (x 0) p q)) := by
      simp only [star_mul,Complex.star_def,Complex.conj_ofReal]
      ring
    rw [heq,hscale]
  · constructor
    · rw [hv]
      simp only [programV,normValue,complexValue_sub,complexValue_mul,ha,hb,hc,he]
      have heq : ((l : ℂ)*polyA d p q)*((l : ℂ)*polyE d (x 0) p q)-
          ((l : ℂ)*polyB d (x 0) p q)*((l : ℂ)*polyC d (x 0) p q)=
          (l : ℂ)^2*(polyA d p q*polyE d (x 0) p q-polyB d (x 0) p q*polyC d (x 0) p q) := by ring
      rw [heq,hscale]
    · rw [hj]
      simp only [programJ,NestedClassPolynomials.pow,NestedClassPolynomials.sub,value,
        normValue,ha,hb,normSq_scaled]
      ring

/-- A single common-denominator certificate supplies the actual Mobius
norm bound for every point of the entire arm parameter box. -/
theorem polynomial_certificate (d : ℚ) (c₁ c₂ : Fin 5) (x : Fin 3 → ℝ)
    (hd : 0 < (d : ℝ)) (hx : 0 < x 0)
    (h₁ : x 1 ∈ Set.Icc (0 : ℝ) 1) (h₂ : x 2 ∈ Set.Icc (0 : ℝ) 1)
    (ζ : ℂ) (hζ : ‖ζ-Focus.g d (x 0)‖ ≤ Focus.r d (x 0))
    (s L : ℝ) (hs : 0 < s)
    (hcert : L*((1+s)*value (programU d c₁ c₂) x+
      (1+1/s)*value (programV d c₁ c₂) x) ≤ value (programJ d c₁ c₂) x) :
    L ≤ ‖Focus.quotient (x 0) (ArmClasses.parameter (x 0) c₁ (x 1))
      (ArmClasses.parameter (x 0) c₂ (x 2)) ζ‖^2 := by
  obtain ⟨a,ha,hpa⟩ := ArmRationalForm.parameter_enclosure c₁ (x 0) (x 1) hx h₁
  obtain ⟨b,hb,hpb⟩ := ArmRationalForm.parameter_enclosure c₂ (x 0) (x 2) hx h₂
  have hp : x 0 ≤ ArmClasses.parameter (x 0) c₁ (x 1) := by
    rw [hpa]
    have := div_nonneg ha.1 hx.le
    linarith
  have hq : x 0 ≤ ArmClasses.parameter (x 0) c₂ (x 2) := by
    rw [hpb]
    have := div_nonneg hb.1 hx.le
    linarith
  apply ClassNormPolynomials.polynomial_certificate d (x 0) _ _ hd hx hp hq ζ hζ s L hs
  obtain ⟨hu,hv,hj⟩ := programs_sound d c₁ c₂ x hx
  rw [hu,hv,hj] at hcert
  apply (mul_le_mul_iff_right₀ (pow_pos (common_positive c₁ c₂ x hx) 4)).mp
  calc
    _ = L*((1+s)*(value (common c₁ c₂) x^4*U d (x 0) _ _)+
        (1+1/s)*(value (common c₁ c₂) x^4*V d (x 0) _ _)) := by ring
    _ ≤ _ := hcert

#print axioms complexValue_add
#print axioms complexValue_sub
#print axioms complexValue_mul
#print axioms complexValue_star
#print axioms normValue
#print axioms normSq_scaled
#print axioms common_positive
#print axioms programs_sound
#print axioms polynomial_certificate
end
end Gebendorfer.RadenkovicGutman.NestedClassNorms
