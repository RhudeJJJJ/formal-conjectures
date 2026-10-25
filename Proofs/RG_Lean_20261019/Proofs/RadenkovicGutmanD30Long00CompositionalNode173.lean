/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode165
import Proofs.RadenkovicGutmanD30Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-56],[0]],[[0,0],[0]],[[-772,0],[0,0]],[[0,0],[0,0]],[[-4252,0],[0,0]],[[0,0],[0,0]],[[-11576,0],[0,0]],[[0,0],[0,0]],[[-14476,0],[0,0]],[[0,0],[0,0]],[[-624,-56],[-56,0]],[[0,0],[0,0]],[[20300,-418],[-418,0]],[[0,0],[0,0]],[[24088,-1022],[-1022,0]],[[0,0],[0,0]],[[11796,-864],[-864,0]],[[0,0],[0,0]],[[2196,-114],[-114,0]],[[0,0],[0,0]],[[0,90],[90,-56]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
