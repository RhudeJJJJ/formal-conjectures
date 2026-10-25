/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode119
import Proofs.RadenkovicGutmanD15Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-382,0],[0,0]],[[0,0],[0,0]],[[-2332,0],[0,0]],[[0,0],[0,0]],[[-7646,0],[0,0]],[[0,0],[0,0]],[[-14536,0],[0,0]],[[0,0],[0,0]],[[-16104,-26],[-26,0]],[[0,0],[0,0]],[[-9700,-208],[-208,0]],[[0,0],[0,0]],[[-2222,-572],[-572,0]],[[0,0],[0,0]],[[546,-624],[-624,0]],[[0,0],[0,0]],[[306,-234],[-234,0]],[[0],[0,0]],[[0],[0,-26]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
