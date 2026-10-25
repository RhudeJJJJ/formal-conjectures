/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode119
import Proofs.RadenkovicGutmanD30Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-56],[0]],[[0,0],[0]],[[-832,0],[0,0]],[[0,0],[0,0]],[[-5152,0],[0,0]],[[0,0],[0,0]],[[-17216,0],[0,0]],[[0,0],[0,0]],[[-33616,0],[0,0]],[[0,0],[0,0]],[[-38784,-56],[-56,0]],[[0,0],[0,0]],[[-25120,-448],[-448,0]],[[0,0],[0,0]],[[-7232,-1232],[-1232,0]],[[0,0],[0,0]],[[456,-1344],[-1344,0]],[[0,0],[0,0]],[[576,-504],[-504,0]],[[0],[0,0]],[[0],[0,-56]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
