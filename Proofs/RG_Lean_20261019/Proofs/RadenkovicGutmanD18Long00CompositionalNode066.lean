/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode065
import Proofs.RadenkovicGutmanD18Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-18]],[[0,0],[0,0]],[[-162,-270],[-270,-2]],[[0,0],[0]],[[-4500,-918],[-918]],[[0,0],[0]],[[-23664,-1020],[-1020]],[[0,0],[0]],[[-55178,-440],[-440]],[[0,0],[0]],[[-70468,-70],[-70]],[[0,0],[0]],[[-53544,-2],[-2]],[[0]],[[-24898]],[[0]],[[-7010]],[[0]],[[-1126]],[[0]],[[-88]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
