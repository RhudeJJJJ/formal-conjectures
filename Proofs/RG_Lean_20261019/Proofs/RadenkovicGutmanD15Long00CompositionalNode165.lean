/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode164
import Proofs.RadenkovicGutmanD15Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-382,0],[0,0]],[[0,0],[0,0]],[[-2332,0],[0,0]],[[0,0],[0,0]],[[-7646,0],[0,0]],[[0,0],[0,0]],[[-14536,0],[0,0]],[[0,0],[0,0]],[[-16104,-26],[-26,0]],[[0,0],[0,0]],[[-9700,-208],[-208,0]],[[0,0],[0,0]],[[-2222,-572],[-572,0]],[[0,0],[0,0]],[[546,-624],[-624,0]],[[0,0],[0,0]],[[306,-234],[-234,0]],[[0],[0,0]],[[0],[0,-26]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
