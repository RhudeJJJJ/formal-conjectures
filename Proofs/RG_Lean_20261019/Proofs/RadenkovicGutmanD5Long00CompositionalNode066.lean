/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode065
import Proofs.RadenkovicGutmanD5Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-5]],[[0,0],[0,0]],[[-45,-75],[-75,-2]],[[0,0],[0]],[[-1263,-268],[-268]],[[0,0],[0]],[[-6803,-318],[-318]],[[0,0],[0]],[[-16334,-154],[-154]],[[0,0],[0]],[[-21640,-31],[-31]],[[0,0],[0]],[[-17248,-2],[-2]],[[0]],[[-8557]],[[0]],[[-2642]],[[0]],[[-489]],[[0]],[[-49]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
