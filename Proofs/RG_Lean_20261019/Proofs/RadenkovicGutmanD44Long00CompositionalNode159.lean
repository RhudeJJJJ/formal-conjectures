/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode037
import Proofs.RadenkovicGutmanD44Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-630,0],[0,0]],[[0,0],[0,0]],[[-3948,0],[0,0]],[[0,0],[0,0]],[[-13398,0],[0,0]],[[0,0],[0,0]],[[-26712,0],[0,0]],[[0,0],[0,0]],[[-31752,-42],[-42,0]],[[0,0],[0,0]],[[-21588,-336],[-336,0]],[[0,0],[0,0]],[[-7014,-924],[-924,0]],[[0,0],[0,0]],[[-126,-1008],[-1008,0]],[[0,0],[0,0]],[[378,-378],[-378,0]],[[0],[0,0]],[[0],[0,-42]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
