/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode036
import Proofs.RadenkovicGutmanD10Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-16]],[[0,0],[0]],[[216,-144],[-144]],[[0,0],[0]],[[576,-384],[-384]],[[0,0],[0]],[[-552,-352],[-352]],[[0,0],[0]],[[-4560,-128],[-128]],[[0,0],[0]],[[-8544,-16],[-16]],[[0]],[[-8176]],[[0]],[[-4456]],[[0]],[[-1392]],[[0]],[[-232]],[[0]],[[-16]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
