/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanClassCellCertificates
import Proofs.RadenkovicGutmanClassNormPolynomials
namespace Gebendorfer.RadenkovicGutman.DegreeOneClass11Cell
open Finset Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def cu : Fin 15 → ℚ := ![13840,(2432692/175),(794115898/56875),(63809845761/4550000),(50357780027983/3575000000),(229910360600861/16250000000),(1066880015771237237/75075000000000),(51028377859672929907/3575000000000000),(107633372943415750892033/7507500000000000000),(128701607745526566499343/8937500000000000000),(45244807026020330007082751/3128125000000000000000),(826272293445620279937750333/56875000000000000000000),(16598572560691850658203055941/1137500000000000000000000),(91604608884110208102073141501/6250000000000000000000000),(9201014443457482866970733051401/625000000000000000000000000)]
def cv : Fin 15 → ℚ := ![400,(2004/5),(1757008/4375),(9154724897/22750000),(917304998823/2275000000),(72218276201897/178750000000),(151962128066977219/375375000000000),(131832528615158297/325000000000000),(234725706298673434277/577500000000000000),(92653057770465331673/227500000000000000),(29177920163646932229/71500000000000000),(18605008162288265401/45500000000000000),(18642334108537331363/45500000000000000),(7184517467023522803/17500000000000000),(1028419905416380801/2500000000000000)]
def cj : Fin 15 → ℚ := ![25600,(899712/35),(1468090096/56875),(36854360161/1421875),(40707838883913/1564062500),(2043830452432129/78203125000),(307845824813706659/11730468750000),(23552197133192592757/893750000000000),(49664780889439102013441/1876875000000000000),(1662361224033896888395571/62562500000000000000),(166925951717464334259423159/6256250000000000000000),(1523807010066223336368766039/56875000000000000000000),(153013267428207359107049706907/5687500000000000000000000),(168844589981795209267118050101/6250000000000000000000000),(16954576027756552706636457071401/625000000000000000000000000)]
noncomputable def coordinate (y : ℝ) : ℝ := 100*(y-1)
noncomputable def weights (y : ℝ) (i : Fin 15) : ℝ :=
  y^2*Bernstein.basis 14 i (coordinate y)

theorem coefficient_check : ClassCellCertificates.accepts cu cv cj (1/5) (13/10)=true := by decide +kernel
theorem logarithm_check : RationalLog.accepts (13/10) (13/100) 0 12=true := by decide +kernel
theorem representationU (y : ℝ) :
    ClassNormPolynomials.U 1 y y y=∑ i, (cu i : ℝ)*weights y i := by
  norm_num [ClassNormPolynomials.U,ClassNormPolynomials.polyA,ClassNormPolynomials.polyB,ClassNormPolynomials.polyC,ClassNormPolynomials.polyE,
    cu,weights,coordinate,Bernstein.basis,bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  ring
theorem representationV (y : ℝ) :
    ClassNormPolynomials.V 1 y y y=∑ i, (cv i : ℝ)*weights y i := by
  norm_num [ClassNormPolynomials.V,ClassNormPolynomials.polyA,ClassNormPolynomials.polyB,ClassNormPolynomials.polyC,ClassNormPolynomials.polyE,
    cv,weights,coordinate,Bernstein.basis,bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  ring
theorem representationJ (y : ℝ) :
    ClassNormPolynomials.J 1 y y y=∑ i, (cj i : ℝ)*weights y i := by
  norm_num [ClassNormPolynomials.J,ClassNormPolynomials.polyA,ClassNormPolynomials.polyB,
    cj,weights,coordinate,Bernstein.basis,bernsteinPolynomial,Nat.choose,Fin.sum_univ_succ]
  ring
theorem actual_log_lower (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) (101/100))
    (ζ : ℂ) (hζ : ‖ζ-Focus.g 1 y‖ ≤ Focus.r 1 y) :
    (13/100 : ℝ) ≤ Real.log ‖Focus.quotient y y y ζ‖ := by
  have hpos : 0<y := by linarith [hy.1]
  have ht : coordinate y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> dsimp [coordinate] <;> linarith [hy.1,hy.2]
  have hcast : ((13/100 : ℚ) : ℝ)=(13/100 : ℝ) := by norm_num
  rw [← hcast]
  apply ClassCellCertificates.cell_log_lower cu cv cj (1/5) (13/10) (13/100) 0 12
    coefficient_check logarithm_check (weights y)
    (fun i => mul_nonneg (sq_nonneg y) (Bernstein.basis_nonneg _ _ _ ht))
    1 y y y (by norm_num) hpos le_rfl le_rfl ζ hζ
  · rw [← ClassNormPolynomials.U_actual 1 y y y hpos]
    exact representationU y
  · rw [← ClassNormPolynomials.V_actual 1 y y y hpos]
    exact representationV y
  · rw [← ClassNormPolynomials.J_actual 1 y y y hpos]
    exact representationJ y
#print axioms coefficient_check
#print axioms logarithm_check
#print axioms representationU
#print axioms representationV
#print axioms representationJ
#print axioms actual_log_lower
end Gebendorfer.RadenkovicGutman.DegreeOneClass11Cell
