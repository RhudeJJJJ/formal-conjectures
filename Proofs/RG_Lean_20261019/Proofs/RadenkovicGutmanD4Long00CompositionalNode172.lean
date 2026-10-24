/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode164
import Proofs.RadenkovicGutmanD4Long00CompositionalNode171
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .plus e164 e171
noncomputable def p172 : NestedHorner.Poly 3 := [[[-4],[0]],[[0,0],[0]],[[-44,0],[0,0]],[[0,0],[0,0]],[[-144,0],[0,0]],[[0,0],[0,0]],[[124,0],[0,0]],[[0,0],[0,0]],[[2008,0],[0,0]],[[0,0],[0,0]],[[5616,-4],[-4,0]],[[0,0],[0,0]],[[7664,-28],[-28,0]],[[0,0],[0,0]],[[5628,-60],[-60,0]],[[0,0],[0,0]],[[2124,-32],[-32,0]],[[0,0],[0,0]],[[324,16],[16,0]],[[0,0],[0,0]],[[0,12],[12,-4]]]
theorem step172 : p172=NestedHorner.add p164 p171 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_plus e172 e164 e171 p164 p171 p172 rfl h164 h171 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
