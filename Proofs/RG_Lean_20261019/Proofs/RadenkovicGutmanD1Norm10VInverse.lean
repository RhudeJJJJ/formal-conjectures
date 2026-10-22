/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNormProgramPack
namespace Gebendorfer.RadenkovicGutman.DegreeOneNormPack10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def vInverse : NestedHorner.Poly 3 := [[[0]],[[0,0]],[[4,0,0]],[[0,0,0,0]],[[160,0,0,0,0]],[[0,0,0,0,0]],[[2976,0,0,0,0]],[[0,0,0,0,0]],[[34176,0,0,0,0]],[[0,0,0,0,0]],[[271344,0,0,0,0]],[[0,0,0,0,0]],[[1580552,8,0,0,0]],[[0,0,0,0,0]],[[6995104,248,0,0,0]],[[0,0,0,0,0]],[[24036368,3488,0,0,0]],[[0,0,0,0,0]],[[64977496,29448,0,0,0]],[[0,0,0,0,0]],[[139196280,166408,0,0,0]],[[0,0,0,0,0]],[[236917860,664440,4,0,0]],[[0,0,0,0,0]],[[319932992,1929016,88,0,0]],[[0,0,0,0,0]],[[340965472,4128192,836,0,0]],[[0,0,0,0,0]],[[284086456,6532880,4488,0,0]],[[0,0,0,0,0]],[[182416824,7601528,14960,0,0]],[[0,0,0,0,0]],[[88436880,6409096,32040,0,0]],[[0,0,0,0,0]],[[31438324,3817336,44132,0,0]],[[0,0,0,0,0]],[[7852584,1542080,38104,0,0]],[[0,0,0,0,0]],[[1289412,395352,19492,0,0]],[[0,0,0,0,0]],[[123552,57024,5280,0,0]],[[0,0,0,0,0]],[[5184,3456,576,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]],[[0,0,0,0,0]]]
theorem vInverse_checked : NestedArithmetic.accepts ((NestedReciprocal.homogenize (NestedClassPolynomials.programV 1 0 4)).2) vInverse=true := by decide +kernel
#print axioms vInverse_checked
theorem vDegree_checked :
    (NestedReciprocal.homogenize (NestedClassPolynomials.programV 1 0 4)).1=48 := by decide +kernel
#print axioms vDegree_checked
end Gebendorfer.RadenkovicGutman.DegreeOneNormPack10
