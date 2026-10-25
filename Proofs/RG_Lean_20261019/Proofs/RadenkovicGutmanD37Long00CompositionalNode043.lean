/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode041
import Proofs.RadenkovicGutmanD37Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,111],[111,-70]],[[0,0],[0]],[[2700,-149],[-149]],[[0,0],[0]],[[14400,-1088],[-1088]],[[0,0],[0]],[[29058,-1281],[-1281]],[[0,0],[0]],[[23702,-523],[-523]],[[0,0],[0]],[[-2304,-70],[-70]],[[0]],[[-18914]],[[0]],[[-14726]],[[0]],[[-5358]],[[0]],[[-968]],[[0]],[[-70]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
