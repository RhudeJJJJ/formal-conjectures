/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode174
import Proofs.RadenkovicGutmanD41Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-78],[0]],[[0,0],[0]],[[-1326,0],[0,0]],[[0,0],[0,0]],[[-9516,0],[0,0]],[[0,0],[0,0]],[[-37518,0],[0,0]],[[0,0],[0,0]],[[-88608,0],[0,0]],[[0,0],[0,0]],[[-128232,-78],[-78,0]],[[0,0],[0,0]],[[-111540,-624],[-624,0]],[[0,0],[0,0]],[[-54366,-1716],[-1716,0]],[[0,0],[0,0]],[[-12402,-1872],[-1872,0]],[[0,0],[0,0]],[[-702,-702],[-702,0]],[[0],[0,0]],[[0],[0,-78]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
