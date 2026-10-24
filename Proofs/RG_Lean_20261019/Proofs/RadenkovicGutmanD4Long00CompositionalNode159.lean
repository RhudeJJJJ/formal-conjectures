/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode158
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e158 e121
noncomputable def p159 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-30,0],[0,0]],[[0,0],[0,0]],[[-188,0],[0,0]],[[0,0],[0,0]],[[-638,0],[0,0]],[[0,0],[0,0]],[[-1272,0],[0,0]],[[0,0],[0,0]],[[-1512,-2],[-2,0]],[[0,0],[0,0]],[[-1028,-16],[-16,0]],[[0,0],[0,0]],[[-334,-44],[-44,0]],[[0,0],[0,0]],[[-6,-48],[-48,0]],[[0,0],[0,0]],[[18,-18],[-18,0]],[[0],[0,0]],[[0],[0,-2]]]
theorem step159 : p159=NestedArithmetic.mul p158 p121 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e158 e121 p158 p121 p159 rfl h158 h121 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
