/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode065
import Proofs.RadenkovicGutmanD6Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-6]],[[0,0],[0,0]],[[-54,-90],[-90,-2]],[[0,0],[0]],[[-1512,-318],[-318]],[[0,0],[0]],[[-8100,-372],[-372]],[[0,0],[0]],[[-19322,-176],[-176]],[[0,0],[0]],[[-25396,-34],[-34]],[[0,0],[0]],[[-20040,-2],[-2]],[[0]],[[-9814]],[[0]],[[-2978]],[[0]],[[-538]],[[0]],[[-52]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
