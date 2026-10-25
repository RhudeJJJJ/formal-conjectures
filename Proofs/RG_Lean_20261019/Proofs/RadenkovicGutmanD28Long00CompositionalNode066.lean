/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode065
import Proofs.RadenkovicGutmanD28Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-28]],[[0,0],[0,0]],[[-252,-420],[-420,-2]],[[0,0],[0]],[[-6990,-1418],[-1418]],[[0,0],[0]],[[-36634,-1560],[-1560]],[[0,0],[0]],[[-85058,-660],[-660]],[[0,0],[0]],[[-108028,-100],[-100]],[[0,0],[0]],[[-81464,-2],[-2]],[[0]],[[-37468]],[[0]],[[-10370]],[[0]],[[-1616]],[[0]],[[-118]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
