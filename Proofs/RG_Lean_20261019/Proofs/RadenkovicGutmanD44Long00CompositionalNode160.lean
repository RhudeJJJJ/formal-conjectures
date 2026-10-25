/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode159
import Proofs.RadenkovicGutmanD44Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-42],[0]],[[0,0],[0]],[[-630,0],[0,0]],[[0,0],[0,0]],[[-3948,0],[0,0]],[[0,0],[0,0]],[[-13398,0],[0,0]],[[0,0],[0,0]],[[-26712,0],[0,0]],[[0,0],[0,0]],[[-31752,-42],[-42,0]],[[0,0],[0,0]],[[-21588,-336],[-336,0]],[[0,0],[0,0]],[[-7014,-924],[-924,0]],[[0,0],[0,0]],[[-126,-1008],[-1008,0]],[[0,0],[0,0]],[[378,-378],[-378,0]],[[0],[0,0]],[[0],[0,-42]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
