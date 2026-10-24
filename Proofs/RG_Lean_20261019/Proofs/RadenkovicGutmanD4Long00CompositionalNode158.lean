/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode036
import Proofs.RadenkovicGutmanD4Long00CompositionalNode157
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e158 : NestedArithmetic.Expr 3 := .times e036 e157
noncomputable def p158 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-30,0],[0,0]],[[0,0],[0,0]],[[-188,0],[0,0]],[[0,0],[0,0]],[[-638,0],[0,0]],[[0,0],[0,0]],[[-1272,0],[0,0]],[[0,0],[0,0]],[[-1512,-2],[-2,0]],[[0,0],[0,0]],[[-1028,-16],[-16,0]],[[0,0],[0,0]],[[-334,-44],[-44,0]],[[0,0],[0,0]],[[-6,-48],[-48,0]],[[0,0],[0,0]],[[18,-18],[-18,0]],[[0],[0,0]],[[0],[0,-2]]]
theorem step158 : p158=NestedArithmetic.mul p036 p157 := by decide +kernel
#print axioms step158
theorem h158 : NestedArithmetic.compile e158=p158 := StagedExprCompile.compile_times e158 e036 e157 p036 p157 p158 rfl h036 h157 step158
#print axioms h158
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
