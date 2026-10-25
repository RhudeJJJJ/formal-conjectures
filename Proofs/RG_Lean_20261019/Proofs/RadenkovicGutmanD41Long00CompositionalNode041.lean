/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode036
import Proofs.RadenkovicGutmanD41Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-78]],[[0,0],[0]],[[774,-702],[-702]],[[0,0],[0]],[[390,-1872],[-1872]],[[0,0],[0]],[[-10906,-1716],[-1716]],[[0,0],[0]],[[-36428,-624],[-624]],[[0,0],[0]],[[-55416,-78],[-78]],[[0]],[[-47608]],[[0]],[[-24234]],[[0]],[[-7220]],[[0]],[[-1162]],[[0]],[[-78]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
