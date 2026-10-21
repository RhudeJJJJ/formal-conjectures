/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRationalTensorFast
namespace Gebendorfer.RadenkovicGutman.UniformTailPolynomials
open RationalTensorPolynomial
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def C (y P Q : ℝ) : ℝ :=
  (1+y^2)*((P*Q-1)^2+(P+Q)^2)-y^2*((P*Q+1)^2+(P+Q-y)^2)
def H (y P Q : ℝ) : ℝ :=
  2*((1+y^2)*((P*Q-1)*(4-y*(P+Q))-(P+Q)*(2*(P+Q)+2*y))-
    y^2*((P*Q+1)*(-y*(P+Q-y))-(P+Q-y)*(2*(P+Q-y))))
def L (y P Q : ℝ) : ℝ :=
  -2*((1+y^2)*(-(P+Q)*(4-y*(P+Q))-(P*Q-1)*(2*(P+Q)+2*y))-
    y^2*((-(P+Q-y))*(-y*(P+Q-y))-(P*Q+1)*(2*(P+Q-y))))
def E (y P Q : ℝ) : ℝ :=
  (1+y^2)*((4-y*(P+Q))^2+(2*(P+Q)+2*y)^2)-
    y^2*((-y*(P+Q-y))^2+(2*(P+Q-y))^2)
def decreasing (y P Q : ℝ) : ℝ := -3*C y P Q-H y P Q
def increasing (y P Q : ℝ) : ℝ := 2*C y P Q*y+L y P Q
def corner (y P Q : ℝ) : ℝ := C y P Q*((3/2)^2+y^2)+H y P Q*(3/2)+L y P Q*y+E y P Q

def CData : Poly 3 := [(2,![0,0,0]),(1,![2,0,0]),(2,![2,0,1]),(1,![2,0,2]),(2,![2,1,0]),(1,![2,2,0]),(1,![4,0,2]),(2,![4,1,2]),(1,![4,2,0]),(2,![4,2,1]),(1,![6,2,2])]
def CDegrees : Fin 3 → ℕ := ![6,2,2]
theorem C_accepted : acceptsFast CDegrees CData=true := by decide +kernel
theorem C_identity (u a b : ℝ) (hu : u ≠ 0) :
    evaluate ![u,a,b] CData=u^2*C (1/u) (1/u+a*u) (1/u+b*u) := by
  norm_num [CData,evaluate,monomial,Fin.prod_univ_succ,C]
  field_simp [hu]
  ring

theorem C_nonneg (y a b : ℝ) (hy : 1 ≤ y) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ C y (y+a/y) (y+b/y) := by
  have hyp : 0<y := by linarith
  have hu : 1/y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hyp).mpr hy
  have hx : ∀ i : Fin 3, (![1/y,a,b] : Fin 3 → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · exact hu
    · exact ha
    · exact hb
  have he := acceptsFast_sound CDegrees CData C_accepted ![1/y,a,b] hx
  rw [C_identity (1/y) a b (by positivity)] at he
  have hp : 0<(1/y)^2 := by positivity
  have hm : 0 ≤ (1/y)^2*C y (y+a/y) (y+b/y) := by
    simpa only [div_eq_mul_inv,one_mul,inv_inv] using he
  exact nonneg_of_mul_nonneg_right hm hp
#print axioms C_accepted
#print axioms C_identity
#print axioms C_nonneg

def decreasingData : Poly 3 := [(2,![0,0,0]),(10,![2,0,0]),(2,![2,0,1]),(2,![2,1,0]),(14,![4,0,0]),(6,![4,0,1]),(6,![4,1,0]),(2,![4,1,1]),(5,![6,0,0]),(4,![6,0,1]),(-1,![6,0,2]),(4,![6,1,0]),(-1,![6,2,0]),(1,![8,0,2]),(-4,![8,1,2]),(1,![8,2,0]),(-4,![8,2,1]),(-3,![10,2,2])]
def decreasingDegrees : Fin 3 → ℕ := ![10,2,2]
theorem decreasing_accepted : acceptsFast decreasingDegrees decreasingData=true := by decide +kernel
theorem decreasing_identity (u a b : ℝ) (hu : u ≠ 0) :
    evaluate ![u,a,b] decreasingData=u^6*decreasing (1/u) (1/u+a*u) (1/u+b*u) := by
  norm_num [decreasingData,evaluate,monomial,Fin.prod_univ_succ,decreasing,C,H]
  field_simp [hu]
  ring

theorem decreasing_nonneg (y a b : ℝ) (hy : 1 ≤ y) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ decreasing y (y+a/y) (y+b/y) := by
  have hyp : 0<y := by linarith
  have hu : 1/y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hyp).mpr hy
  have hx : ∀ i : Fin 3, (![1/y,a,b] : Fin 3 → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · exact hu
    · exact ha
    · exact hb
  have he := acceptsFast_sound decreasingDegrees decreasingData decreasing_accepted ![1/y,a,b] hx
  rw [decreasing_identity (1/y) a b (by positivity)] at he
  have hp : 0<(1/y)^6 := by positivity
  have hm : 0 ≤ (1/y)^6*decreasing y (y+a/y) (y+b/y) := by
    simpa only [div_eq_mul_inv,one_mul,inv_inv] using he
  exact nonneg_of_mul_nonneg_right hm hp
#print axioms decreasing_accepted
#print axioms decreasing_identity
#print axioms decreasing_nonneg

def increasingData : Poly 3 := [(2,![0,0,0]),(8,![2,0,0]),(4,![2,0,1]),(4,![2,1,0]),(6,![4,0,0]),(12,![4,0,1]),(2,![4,0,2]),(12,![4,1,0]),(8,![4,1,1]),(2,![4,2,0]),(4,![6,0,1]),(4,![6,0,2]),(4,![6,1,0]),(16,![6,1,1]),(4,![6,1,2]),(4,![6,2,0]),(4,![6,2,1]),(4,![8,1,2]),(4,![8,2,1]),(2,![8,2,2])]
def increasingDegrees : Fin 3 → ℕ := ![8,2,2]
theorem increasing_accepted : acceptsFast increasingDegrees increasingData=true := by decide +kernel
theorem increasing_identity (u a b : ℝ) (hu : u ≠ 0) :
    evaluate ![u,a,b] increasingData=u^5*increasing (1/u) (1/u+a*u) (1/u+b*u) := by
  norm_num [increasingData,evaluate,monomial,Fin.prod_univ_succ,increasing,C,L]
  field_simp [hu]
  ring

theorem increasing_nonneg (y a b : ℝ) (hy : 1 ≤ y) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ increasing y (y+a/y) (y+b/y) := by
  have hyp : 0<y := by linarith
  have hu : 1/y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hyp).mpr hy
  have hx : ∀ i : Fin 3, (![1/y,a,b] : Fin 3 → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · exact hu
    · exact ha
    · exact hb
  have he := acceptsFast_sound increasingDegrees increasingData increasing_accepted ![1/y,a,b] hx
  rw [increasing_identity (1/y) a b (by positivity)] at he
  have hp : 0<(1/y)^5 := by positivity
  have hm : 0 ≤ (1/y)^5*increasing y (y+a/y) (y+b/y) := by
    simpa only [div_eq_mul_inv,one_mul,inv_inv] using he
  exact nonneg_of_mul_nonneg_right hm hp
#print axioms increasing_accepted
#print axioms increasing_identity
#print axioms increasing_nonneg

def cornerData : Poly 3 := [(2,![0,0,0]),(11,![2,0,0]),(3,![2,0,1]),(3,![2,1,0]),((31/2),![4,0,0]),(13,![4,0,1]),(1,![4,0,2]),(13,![4,1,0]),(5,![4,1,1]),(1,![4,2,0]),((25/4),![6,0,0]),((19/2),![6,0,1]),((13/4),![6,0,2]),((19/2),![6,1,0]),(18,![6,1,1]),(2,![6,1,2]),((13/4),![6,2,0]),(2,![6,2,1]),((1/4),![8,0,2]),(8,![8,1,1]),((11/2),![8,1,2]),((1/4),![8,2,0]),((11/2),![8,2,1]),(1,![8,2,2]),((9/4),![10,2,2])]
def cornerDegrees : Fin 3 → ℕ := ![10,2,2]
theorem corner_accepted : acceptsFast cornerDegrees cornerData=true := by decide +kernel
theorem corner_identity (u a b : ℝ) (hu : u ≠ 0) :
    evaluate ![u,a,b] cornerData=u^6*corner (1/u) (1/u+a*u) (1/u+b*u) := by
  norm_num [cornerData,evaluate,monomial,Fin.prod_univ_succ,corner,C,H,L,E]
  field_simp [hu]
  ring

theorem corner_nonneg (y a b : ℝ) (hy : 1 ≤ y) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ corner y (y+a/y) (y+b/y) := by
  have hyp : 0<y := by linarith
  have hu : 1/y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hyp).mpr hy
  have hx : ∀ i : Fin 3, (![1/y,a,b] : Fin 3 → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · exact hu
    · exact ha
    · exact hb
  have he := acceptsFast_sound cornerDegrees cornerData corner_accepted ![1/y,a,b] hx
  rw [corner_identity (1/y) a b (by positivity)] at he
  have hp : 0<(1/y)^6 := by positivity
  have hm : 0 ≤ (1/y)^6*corner y (y+a/y) (y+b/y) := by
    simpa only [div_eq_mul_inv,one_mul,inv_inv] using he
  exact nonneg_of_mul_nonneg_right hm hp
#print axioms corner_accepted
#print axioms corner_identity
#print axioms corner_nonneg
end
end Gebendorfer.RadenkovicGutman.UniformTailPolynomials
