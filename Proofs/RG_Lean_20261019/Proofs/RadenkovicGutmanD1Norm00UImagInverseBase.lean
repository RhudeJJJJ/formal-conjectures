/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanInverseNormCompilation
namespace Gebendorfer.RadenkovicGutman.DegreeOneNormPack00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def uImagProgram : NestedArithmetic.Expr 3 := (NestedClassPolynomials.csub (NestedClassPolynomials.cmul (NestedClassPolynomials.coeffB 1 4 4) (NestedClassPolynomials.cstar (NestedClassPolynomials.coeffE 1 4 4))) (NestedClassPolynomials.cmul (NestedClassPolynomials.coeffA 1 4 4) (NestedClassPolynomials.cstar (NestedClassPolynomials.coeffC 1 4 4)))).2
def uImagInverse : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[-6,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-202,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-3134,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-29720,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-192660,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-904626,-6,0],[-6,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-3180810,-148,0],[-148,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-8540728,-1634,0],[-1634,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-17700500,-10660,0],[-10660,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-28432388,-45698,0],[-45698,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-35349722,-135448,0],[-135448,-6,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-33789696,-284484,0],[-284484,-92,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-24517924,-427032,0],[-427032,-598,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-13232058,-456410,0],[-456410,-2148,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-5146838,-341876,0],[-341876,-4664,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-1372992,-173930,0],[-173930,-6300,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-230958,-56772,0],[-56772,-5254,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-20790,-10638,0],[-10638,-2588,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[-648,-864,0],[-864,-678,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-72,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]]]
theorem uImagInverse_checked : NestedArithmetic.accepts
    (NestedReciprocal.homogenize uImagProgram).2 uImagInverse=true := by decide +kernel
theorem uImagDegree_checked : (NestedReciprocal.homogenize uImagProgram).1=43 := by decide +kernel
#print axioms uImagInverse_checked
#print axioms uImagDegree_checked
end Gebendorfer.RadenkovicGutman.DegreeOneNormPack00
