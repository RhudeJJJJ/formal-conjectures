/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode165
import Proofs.RadenkovicGutmanD41Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-78],[0]],[[0,0],[0]],[[-1080,0],[0,0]],[[0,0],[0,0]],[[-5990,0],[0,0]],[[0,0],[0,0]],[[-16526,0],[0,0]],[[0,0],[0,0]],[[-21450,0],[0,0]],[[0,0],[0,0]],[[-3264,-78],[-78,0]],[[0,0],[0,0]],[[25646,-583],[-583,0]],[[0,0],[0,0]],[[31898,-1429],[-1429,0]],[[0,0],[0,0]],[[15888,-1216],[-1216,0]],[[0,0],[0,0]],[[2988,-169],[-169,0]],[[0,0],[0,0]],[[0,123],[123,-78]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
