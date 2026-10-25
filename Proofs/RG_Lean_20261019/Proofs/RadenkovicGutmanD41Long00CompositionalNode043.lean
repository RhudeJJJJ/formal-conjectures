/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode041
import Proofs.RadenkovicGutmanD41Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,123],[123,-78]],[[0,0],[0]],[[2988,-169],[-169]],[[0,0],[0]],[[15888,-1216],[-1216]],[[0,0],[0]],[[31898,-1429],[-1429]],[[0,0],[0]],[[25646,-583],[-583]],[[0,0],[0]],[[-3264,-78],[-78]],[[0]],[[-21450]],[[0]],[[-16526]],[[0]],[[-5990]],[[0]],[[-1080]],[[0]],[[-78]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
