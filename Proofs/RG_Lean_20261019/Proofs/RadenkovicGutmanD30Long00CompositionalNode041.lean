/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode036
import Proofs.RadenkovicGutmanD30Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-56]],[[0,0],[0]],[[576,-504],[-504]],[[0,0],[0]],[[456,-1344],[-1344]],[[0,0],[0]],[[-7232,-1232],[-1232]],[[0,0],[0]],[[-25120,-448],[-448]],[[0,0],[0]],[[-38784,-56],[-56]],[[0]],[[-33616]],[[0]],[[-17216]],[[0]],[[-5152]],[[0]],[[-832]],[[0]],[[-56]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
