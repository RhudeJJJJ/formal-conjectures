/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanInverseNormCompilation
namespace Gebendorfer.RadenkovicGutman.DegreeOneNormPack00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def uRealProgram : NestedArithmetic.Expr 3 := (NestedClassPolynomials.csub (NestedClassPolynomials.cmul (NestedClassPolynomials.coeffB 1 4 4) (NestedClassPolynomials.cstar (NestedClassPolynomials.coeffE 1 4 4))) (NestedClassPolynomials.cmul (NestedClassPolynomials.coeffA 1 4 4) (NestedClassPolynomials.cstar (NestedClassPolynomials.coeffC 1 4 4)))).1
def uRealInverse : NestedHorner.Poly 3 := [[[4],[0],[0]],[[0,0],[0,0],[0]],[[156,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2816,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[31236,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[238368,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[1327624,8,0],[8,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[5587128,236,0],[236,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[18145620,3148,0],[3148,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[46054488,25120,0],[25120,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[91928608,133692,0],[133692,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[144508104,500892,4],[500892,16,0],[4,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[178310692,1359092,80],[1359092,324,0],[80,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[171311840,2706084,692],[2706084,2832,0],[692,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[126388728,3962448,3392],[3962448,14004,0],[3392,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[70081608,4234256,10372],[4234256,43136,0],[10372,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[28263692,3240884,20528],[3240884,85888,8],[20528,8,0]],[[0,0,0],[0,0,0],[0,0,0]],[[7875492,1717684,26408],[1717684,111016,88],[26408,88,0]],[[0,0,0],[0,0,0],[0,0,0]],[[1391364,594476,21568],[594476,90996,368],[21568,368,0]],[[0,0,0],[0,0,0],[0,0,0]],[[132408,120600,10528],[120600,44544,728],[10528,728,0]],[[0,0,0],[0,0,0],[0,0,0]],[[4536,11340,2688],[11340,11412,688],[2688,688,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,216,252],[216,1080,272],[252,272,4]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,24],[0,24,8]],[[0],[0,0],[0,0,0]],[[0],[0,0],[0,0,0]]]
theorem uRealInverse_checked : NestedArithmetic.accepts
    (NestedReciprocal.homogenize uRealProgram).2 uRealInverse=true := by decide +kernel
theorem uRealDegree_checked : (NestedReciprocal.homogenize uRealProgram).1=44 := by decide +kernel
#print axioms uRealInverse_checked
#print axioms uRealDegree_checked
end Gebendorfer.RadenkovicGutman.DegreeOneNormPack00
