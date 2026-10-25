/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode036
import Proofs.RadenkovicGutmanD20Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-36]],[[0,0],[0]],[[396,-324],[-324]],[[0,0],[0]],[[516,-864],[-864]],[[0,0],[0]],[[-3892,-792],[-792]],[[0,0],[0]],[[-14840,-288],[-288]],[[0,0],[0]],[[-23664,-36],[-36]],[[0]],[[-20896]],[[0]],[[-10836]],[[0]],[[-3272]],[[0]],[[-532]],[[0]],[[-36]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
