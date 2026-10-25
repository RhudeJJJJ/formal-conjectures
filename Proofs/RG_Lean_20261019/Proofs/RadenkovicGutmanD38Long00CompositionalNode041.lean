/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode036
import Proofs.RadenkovicGutmanD38Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-72]],[[0,0],[0]],[[720,-648],[-648]],[[0,0],[0]],[[408,-1728],[-1728]],[[0,0],[0]],[[-9904,-1584],[-1584]],[[0,0],[0]],[[-33344,-576],[-576]],[[0,0],[0]],[[-50880,-72],[-72]],[[0]],[[-43792]],[[0]],[[-22320]],[[0]],[[-6656]],[[0]],[[-1072]],[[0]],[[-72]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
