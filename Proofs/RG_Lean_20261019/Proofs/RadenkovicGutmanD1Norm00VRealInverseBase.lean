/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanInverseNormCompilation
namespace Gebendorfer.RadenkovicGutman.DegreeOneNormPack00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def vRealProgram : NestedArithmetic.Expr 3 := (NestedClassPolynomials.csub (NestedClassPolynomials.cmul (NestedClassPolynomials.coeffA 1 4 4) (NestedClassPolynomials.coeffE 1 4 4)) (NestedClassPolynomials.cmul (NestedClassPolynomials.coeffB 1 4 4) (NestedClassPolynomials.coeffC 1 4 4))).1
def vRealInverse : NestedHorner.Poly 3 := [[[2],[0],[0]],[[0,0],[0,0],[0]],[[54,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[634,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[4104,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[14364,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[10462,2,0],[2,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-162258,36,0],[36,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-967640,254,0],[254,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-3105044,740,0],[740,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-6753652,-698,0],[-698,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-10598834,-13408,0],[-13408,2,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-12251296,-51788,0],[-51788,20,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-10448916,-113048,0],[-113048,50,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-6500106,-158538,0],[-158538,-148,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-2875886,-147068,0],[-147068,-1112,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-865824,-89250,0],[-89250,-2636,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-164214,-33804,0],[-33804,-3134,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-16902,-7182,0],[-7182,-1964,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-648,-648,0],[-648,-606,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-72,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]]]
theorem vRealInverse_checked : NestedArithmetic.accepts
    (NestedReciprocal.homogenize vRealProgram).2 vRealInverse=true := by decide +kernel
theorem vRealDegree_checked : (NestedReciprocal.homogenize vRealProgram).1=41 := by decide +kernel
#print axioms vRealInverse_checked
#print axioms vRealDegree_checked
end Gebendorfer.RadenkovicGutman.DegreeOneNormPack00
