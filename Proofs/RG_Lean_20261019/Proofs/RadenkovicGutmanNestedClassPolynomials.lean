/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedArithmetic
import Proofs.RadenkovicGutmanArmRationalForm
import Proofs.RadenkovicGutmanClassNormPolynomials

namespace Gebendorfer.RadenkovicGutman.NestedClassPolynomials
open NestedArithmetic
set_option maxHeartbeats 0
set_option maxRecDepth 100000

abbrev P := Expr 3
def rat (q : ℚ) : P := .rational q
def y : P := .indet 0
def add (a b : P) : P := .plus a b
def sub (a b : P) : P := .plus a (.scaled (-1) b)
def mul (a b : P) : P := .times a b
def pow (a : P) (k : ℕ) : P := .pow a k
local infixl:65 " +ₚ " => add
local infixl:65 " -ₚ " => sub
local infixl:70 " *ₚ " => mul

/-- The class indices are precisely those of ArmClasses.parameter. -/
def armDen (c : Fin 5) : P :=
  if c.val=0 then rat 1 else if c.val=1 then y
  else if c.val=2 then pow y 2 +ₚ rat 1
  else if c.val=3 then pow y 3 +ₚ rat 2 *ₚ y
  else y *ₚ (pow y 4 +ₚ rat 3 *ₚ pow y 2 +ₚ rat 1) *ₚ
    (pow y 4 +ₚ rat 4 *ₚ pow y 2 +ₚ rat 3)

def armNum (c : Fin 5) (i : Fin 3) : P :=
  if c.val=0 then y else if c.val=1 then pow y 2 +ₚ rat 1
  else if c.val=2 then pow y 3 +ₚ rat 2 *ₚ y
  else if c.val=3 then pow y 4 +ₚ rat 3 *ₚ pow y 2 +ₚ rat 1
  else pow y 2 *ₚ (pow y 4 +ₚ rat 3 *ₚ pow y 2 +ₚ rat 1) *ₚ
    (pow y 4 +ₚ rat 4 *ₚ pow y 2 +ₚ rat 3) +ₚ
    (pow y 4 +ₚ rat 2 *ₚ pow y 2) *ₚ (pow y 4 +ₚ rat 4 *ₚ pow y 2 +ₚ rat 3) +ₚ .indet i

abbrev CP := P × P
def cadd (a b : CP) : CP := (a.1 +ₚ b.1,a.2 +ₚ b.2)
def csub (a b : CP) : CP := (a.1 -ₚ b.1,a.2 -ₚ b.2)
def cmul (a b : CP) : CP := (a.1 *ₚ b.1 -ₚ a.2 *ₚ b.2,a.1 *ₚ b.2 +ₚ a.2 *ₚ b.1)
def cstar (a : CP) : CP := (a.1,rat (-1) *ₚ a.2)
def cnorm (a : CP) : P := pow a.1 2 +ₚ pow a.2 2

def common (c₁ c₂ : Fin 5) : P := armDen c₁ *ₚ armDen c₂
def sumNum (c₁ c₂ : Fin 5) : P := armNum c₁ 1 *ₚ armDen c₂ +ₚ armNum c₂ 2 *ₚ armDen c₁
def prodNum (c₁ c₂ : Fin 5) : P := armNum c₁ 1 *ₚ armNum c₂ 2

def coeffA (d : ℚ) (c₁ c₂ : Fin 5) : CP :=
  (rat d *ₚ (prodNum c₁ c₂ -ₚ common c₁ c₂),rat (-d) *ₚ sumNum c₁ c₂)
def coeffB (d : ℚ) (c₁ c₂ : Fin 5) : CP :=
  (rat 2 *ₚ y *ₚ (rat (2-d) *ₚ (prodNum c₁ c₂ -ₚ common c₁ c₂) +ₚ rat 4 *ₚ common c₁ c₂) +ₚ rat d *ₚ sumNum c₁ c₂,
   (rat 2 *ₚ pow y 2 +ₚ rat d) *ₚ (prodNum c₁ c₂ -ₚ common c₁ c₂) +ₚ
      rat (2*d) *ₚ y *ₚ sumNum c₁ c₂ +ₚ rat 4 *ₚ pow y 2 *ₚ common c₁ c₂)
def coeffC (d : ℚ) (c₁ c₂ : Fin 5) : CP :=
  (rat d *ₚ (prodNum c₁ c₂ +ₚ common c₁ c₂),
   rat (-d) *ₚ (sumNum c₁ c₂ -ₚ y *ₚ common c₁ c₂))
def coeffE (d : ℚ) (c₁ c₂ : Fin 5) : CP :=
  (rat 2 *ₚ y *ₚ rat (2-d) *ₚ (prodNum c₁ c₂ +ₚ common c₁ c₂) +ₚ
      rat d *ₚ (sumNum c₁ c₂ -ₚ y *ₚ common c₁ c₂),
   (rat 2 *ₚ pow y 2 +ₚ rat d) *ₚ (prodNum c₁ c₂ +ₚ common c₁ c₂) +ₚ
      rat (2*d) *ₚ y *ₚ (sumNum c₁ c₂ -ₚ y *ₚ common c₁ c₂))

def programU (d : ℚ) (c₁ c₂ : Fin 5) : P :=
  cnorm (csub (cmul (coeffB d c₁ c₂) (cstar (coeffE d c₁ c₂)))
    (cmul (coeffA d c₁ c₂) (cstar (coeffC d c₁ c₂))))
def programV (d : ℚ) (c₁ c₂ : Fin 5) : P :=
  cnorm (csub (cmul (coeffA d c₁ c₂) (coeffE d c₁ c₂))
    (cmul (coeffB d c₁ c₂) (coeffC d c₁ c₂)))
def programJ (d : ℚ) (c₁ c₂ : Fin 5) : P :=
  pow (cnorm (coeffB d c₁ c₂) -ₚ cnorm (coeffA d c₁ c₂)) 2

noncomputable section
def complexValue (a : CP) (x : Fin 3 → ℝ) : ℂ := ⟨value a.1 x,value a.2 x⟩

theorem armDen_sound (c : Fin 5) (x : Fin 3 → ℝ) :
    value (armDen c) x=ArmRationalForm.denominator c (x 0) := by
  fin_cases c <;> norm_num [armDen,ArmRationalForm.denominator,rat,y,add,mul,pow,value]

theorem armNum_sound (c : Fin 5) (i : Fin 3) (x : Fin 3 → ℝ) :
    value (armNum c i) x=ArmRationalForm.numerator c (x 0) (x i) := by
  fin_cases c <;> norm_num [armNum,ArmRationalForm.numerator,rat,y,add,mul,pow,value]

theorem armNum_cleared (c : Fin 5) (i : Fin 3) (x : Fin 3 → ℝ) (hx : 0 < x 0) :
    value (armNum c i) x=value (armDen c) x*ArmClasses.parameter (x 0) c (x i) := by
  rw [armDen_sound,armNum_sound,ArmRationalForm.parameter_identity c (x 0) (x i) hx]
  have h := ArmRationalForm.denominator_positive c (x 0) hx
  field_simp

theorem coefficients_sound (d : ℚ) (c₁ c₂ : Fin 5) (x : Fin 3 → ℝ) (hx : 0 < x 0) :
    let l := value (common c₁ c₂) x
    let p := ArmClasses.parameter (x 0) c₁ (x 1)
    let q := ArmClasses.parameter (x 0) c₂ (x 2)
    complexValue (coeffA d c₁ c₂) x=(l : ℂ)*ClassNormPolynomials.polyA d p q ∧
    complexValue (coeffB d c₁ c₂) x=(l : ℂ)*ClassNormPolynomials.polyB d (x 0) p q ∧
    complexValue (coeffC d c₁ c₂) x=(l : ℂ)*ClassNormPolynomials.polyC d (x 0) p q ∧
    complexValue (coeffE d c₁ c₂) x=(l : ℂ)*ClassNormPolynomials.polyE d (x 0) p q := by
  have h₁ := armNum_cleared c₁ 1 x hx
  have h₂ := armNum_cleared c₂ 2 x hx
  dsimp only
  constructor
  · apply Complex.ext <;> simp only [complexValue,coeffA,common,prodNum,sumNum,
      rat,add,sub,mul,value,h₁,h₂,ClassNormPolynomials.polyA,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Rat.cast_neg] <;> ring
  · constructor
    · apply Complex.ext <;> simp only [complexValue,coeffB,common,prodNum,sumNum,
        rat,y,add,sub,mul,pow,value,h₁,h₂,ClassNormPolynomials.polyB,
        Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Rat.cast_mul,Rat.cast_sub,Rat.cast_ofNat] <;> ring
    · constructor
      · apply Complex.ext <;> simp only [complexValue,coeffC,common,prodNum,sumNum,
          rat,y,add,sub,mul,value,h₁,h₂,ClassNormPolynomials.polyC,
          Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
          Rat.cast_neg] <;> ring
      · apply Complex.ext <;> simp only [complexValue,coeffE,common,prodNum,sumNum,
          rat,y,add,sub,mul,pow,value,h₁,h₂,ClassNormPolynomials.polyE,
          Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
          Rat.cast_mul,Rat.cast_sub,Rat.cast_ofNat] <;> ring

#print axioms armDen_sound
#print axioms armNum_sound
#print axioms armNum_cleared
#print axioms coefficients_sound
end
end Gebendorfer.RadenkovicGutman.NestedClassPolynomials
