/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode177
import Proofs.RadenkovicGutmanD41Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-78],[0]],[[0,0],[0]],[[-1326,0],[0,0]],[[0,0],[0,0]],[[-9516,0],[0,0]],[[0,0],[0,0]],[[-37518,0],[0,0]],[[0,0],[0,0]],[[-88608,0],[0,0]],[[0,0],[0,0]],[[-128232,-78],[-78,0]],[[0,0],[0,0]],[[-111540,-624],[-624,0]],[[0,0],[0,0]],[[-54366,-1716],[-1716,0]],[[0,0],[0,0]],[[-12402,-1872],[-1872,0]],[[0,0],[0,0]],[[-702,-702],[-702,0]],[[0],[0,0]],[[0],[0,-78]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
