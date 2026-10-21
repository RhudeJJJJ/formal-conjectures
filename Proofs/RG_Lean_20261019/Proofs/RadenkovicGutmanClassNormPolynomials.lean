/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanScaledQuotient

/-! Polynomial representatives of the three actual scaled norm expressions.
The identities hold for every positive ordinate and arbitrary real parameters.
Concrete arm substitution, cell coverage and integral payments remain required. -/
namespace Gebendorfer.RadenkovicGutman.ClassNormPolynomials
open Focus
noncomputable section
set_option maxHeartbeats 0

def polyA (d P Q : ℝ) : ℂ := ⟨d*(P*Q-1),-d*(P+Q)⟩
def polyB (d y P Q : ℝ) : ℂ :=
  ⟨2*y*((2-d)*(P*Q-1)+4)+d*(P+Q),
   (2*y^2+d)*(P*Q-1)+2*d*y*(P+Q)+4*y^2⟩
def polyC (d y P Q : ℝ) : ℂ := ⟨d*(P*Q+1),-d*(P+Q-y)⟩
def polyE (d y P Q : ℝ) : ℂ :=
  ⟨2*y*(2-d)*(P*Q+1)+d*(P+Q-y),
   (2*y^2+d)*(P*Q+1)+2*d*y*(P+Q-y)⟩

theorem a_eq (d P Q : ℝ) : a d P Q=polyA d P Q := by
  apply Complex.ext <;> simp [a,A,polyA] <;> ring
theorem c_eq (d y P Q : ℝ) : c d y P Q=polyC d y P Q := by
  apply Complex.ext <;> simp [c,B,polyC] <;> ring
theorem b_eq (d y P Q : ℝ) (hy : 0<y) : b d y P Q=polyB d y P Q := by
  apply Complex.ext <;> simp [b,A,g,N₀,z,polyB] <;> field_simp [hy.ne'] <;> ring
theorem e_eq (d y P Q : ℝ) (hy : 0<y) : e d y P Q=polyE d y P Q := by
  apply Complex.ext <;> simp [e,B,g,D₀,z,polyE] <;> field_simp [hy.ne'] <;> ring

def U (d y P Q : ℝ) : ℝ :=
  let ar := (polyA d P Q).re; let ai := (polyA d P Q).im
  let br := (polyB d y P Q).re; let bi := (polyB d y P Q).im
  let cr := (polyC d y P Q).re; let ci := (polyC d y P Q).im
  let er := (polyE d y P Q).re; let ei := (polyE d y P Q).im
  (br*er+bi*ei-ar*cr-ai*ci)^2+(bi*er-br*ei-ai*cr+ar*ci)^2
def V (d y P Q : ℝ) : ℝ :=
  let ar := (polyA d P Q).re; let ai := (polyA d P Q).im
  let br := (polyB d y P Q).re; let bi := (polyB d y P Q).im
  let cr := (polyC d y P Q).re; let ci := (polyC d y P Q).im
  let er := (polyE d y P Q).re; let ei := (polyE d y P Q).im
  (ar*er-ai*ei-br*cr+bi*ci)^2+(ar*ei+ai*er-br*ci-bi*cr)^2
def J (d y P Q : ℝ) : ℝ :=
  ((polyB d y P Q).re^2+(polyB d y P Q).im^2-
    (polyA d P Q).re^2-(polyA d P Q).im^2)^2

theorem U_actual (d y P Q : ℝ) (hy : 0<y) :
    U d y P Q=‖b d y P Q*star (e d y P Q)-a d P Q*star (c d y P Q)‖^2 := by
  rw [a_eq,b_eq d y P Q hy,c_eq,e_eq d y P Q hy]
  simp [U,Complex.sq_norm,Complex.normSq_apply,Complex.star_def]
  ring
theorem V_actual (d y P Q : ℝ) (hy : 0<y) :
    V d y P Q=‖a d P Q*e d y P Q-b d y P Q*c d y P Q‖^2 := by
  rw [a_eq,b_eq d y P Q hy,c_eq,e_eq d y P Q hy]
  simp [V,Complex.sq_norm,Complex.normSq_apply]
  ring
theorem J_actual (d y P Q : ℝ) (hy : 0<y) :
    J d y P Q=(Complex.normSq (b d y P Q)-Complex.normSq (a d P Q))^2 := by
  rw [a_eq,b_eq d y P Q hy]
  simp [J,Complex.normSq_apply]
  ring

theorem polynomial_certificate (d y P Q : ℝ) (hd : 0<d) (hy : 0<y)
    (hP : y≤P) (hQ : y≤Q) (ζ : ℂ) (hζ : ‖ζ-g d y‖≤r d y)
    (s L : ℝ) (hs : 0<s)
    (hc : L*((1+s)*U d y P Q+(1+1/s)*V d y P Q)≤J d y P Q) :
    L≤‖quotient y P Q ζ‖^2 := by
  apply concrete_certificate d y P Q hd hy hP hQ ζ hζ s L hs
  rw [← U_actual d y P Q hy,← V_actual d y P Q hy,← J_actual d y P Q hy]
  exact hc

#print axioms a_eq
#print axioms b_eq
#print axioms c_eq
#print axioms e_eq
#print axioms U_actual
#print axioms V_actual
#print axioms J_actual
#print axioms polynomial_certificate
end
end Gebendorfer.RadenkovicGutman.ClassNormPolynomials
