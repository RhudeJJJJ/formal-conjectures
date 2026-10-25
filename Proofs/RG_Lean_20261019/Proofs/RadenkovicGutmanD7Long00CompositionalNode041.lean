/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode036
import Proofs.RadenkovicGutmanD7Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-10]],[[0,0],[0]],[[162,-90],[-90]],[[0,0],[0]],[[594,-240],[-240]],[[0,0],[0]],[[450,-220],[-220]],[[0,0],[0]],[[-1476,-80],[-80]],[[0,0],[0]],[[-4008,-10],[-10]],[[0]],[[-4360]],[[0]],[[-2542]],[[0]],[[-828]],[[0]],[[-142]],[[0]],[[-10]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
