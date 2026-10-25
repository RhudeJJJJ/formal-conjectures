/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode178
import Proofs.RadenkovicGutmanD11Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-295,0],[0,0]],[[0,0],[0,0]],[[-2020,0],[0,0]],[[0,0],[0,0]],[[-7481,0],[0,0]],[[0,0],[0,0]],[[-16180,0],[0,0]],[[0,0],[0,0]],[[-20484,-18],[-18,0]],[[0,0],[0,0]],[[-14124,-133],[-133,0]],[[0,0],[0,0]],[[-3977,-319],[-319,0]],[[0,0],[0,0]],[[438,-256],[-256,0]],[[0,0],[0,0]],[[333,-19],[-19,0]],[[0,0],[0,0]],[[0,33],[33,-18]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
