/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode036
import Proofs.RadenkovicGutmanD24Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-44]],[[0,0],[0]],[[468,-396],[-396]],[[0,0],[0]],[[492,-1056],[-1056]],[[0,0],[0]],[[-5228,-968],[-968]],[[0,0],[0]],[[-18952,-352],[-352]],[[0,0],[0]],[[-29712,-44],[-44]],[[0]],[[-25984]],[[0]],[[-13388]],[[0]],[[-4024]],[[0]],[[-652]],[[0]],[[-44]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
