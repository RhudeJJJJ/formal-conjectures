/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode036
import Proofs.RadenkovicGutmanD23Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-42]],[[0,0],[0]],[[450,-378],[-378]],[[0,0],[0]],[[498,-1008],[-1008]],[[0,0],[0]],[[-4894,-924],[-924]],[[0,0],[0]],[[-17924,-336],[-336]],[[0,0],[0]],[[-28200,-42],[-42]],[[0]],[[-24712]],[[0]],[[-12750]],[[0]],[[-3836]],[[0]],[[-622]],[[0]],[[-42]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
