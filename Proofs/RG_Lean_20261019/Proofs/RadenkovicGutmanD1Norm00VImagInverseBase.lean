/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanInverseNormCompilation
namespace Gebendorfer.RadenkovicGutman.DegreeOneNormPack00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def vImagProgram : NestedArithmetic.Expr 3 := (NestedClassPolynomials.csub (NestedClassPolynomials.cmul (NestedClassPolynomials.coeffA 1 4 4) (NestedClassPolynomials.coeffE 1 4 4)) (NestedClassPolynomials.cmul (NestedClassPolynomials.coeffB 1 4 4) (NestedClassPolynomials.coeffC 1 4 4))).2
def vImagInverse : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[-8,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-248,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-3528,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-30528,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-179568,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-760120,-8,0],[-8,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-2391448,-176,0],[-176,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-5695232,-1720,0],[-1720,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-10360752,-9840,0],[-9840,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-14428400,-36568,0],[-36568,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-15318264,-92640,0],[-92640,-8,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-12267872,-163408,0],[-163408,-112,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-7275824,-201440,0],[-201440,-648,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-3102872,-171608,0],[-171608,-2000,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-907944,-98160,0],[-98160,-3552,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-168480,-35640,0],[-35640,-3664,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-17064,-7344,0],[-7344,-2120,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-648,-648,0],[-648,-624,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-72,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0],[0,0],[0,0,0]],[[0],[0,0],[0,0,0]]]
theorem vImagInverse_checked : NestedArithmetic.accepts
    (NestedReciprocal.homogenize vImagProgram).2 vImagInverse=true := by decide +kernel
theorem vImagDegree_checked : (NestedReciprocal.homogenize vImagProgram).1=42 := by decide +kernel
#print axioms vImagInverse_checked
#print axioms vImagDegree_checked
end Gebendorfer.RadenkovicGutman.DegreeOneNormPack00
