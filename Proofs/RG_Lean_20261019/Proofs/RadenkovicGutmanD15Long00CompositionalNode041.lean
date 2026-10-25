/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode036
import Proofs.RadenkovicGutmanD15Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-26]],[[0,0],[0]],[[306,-234],[-234]],[[0,0],[0]],[[546,-624],[-624]],[[0,0],[0]],[[-2222,-572],[-572]],[[0,0],[0]],[[-9700,-208],[-208]],[[0,0],[0]],[[-16104,-26],[-26]],[[0]],[[-14536]],[[0]],[[-7646]],[[0]],[[-2332]],[[0]],[[-382]],[[0]],[[-26]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
