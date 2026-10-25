/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode159
import Proofs.RadenkovicGutmanD28Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-390,0],[0,0]],[[0,0],[0,0]],[[-2444,0],[0,0]],[[0,0],[0,0]],[[-8294,0],[0,0]],[[0,0],[0,0]],[[-16536,0],[0,0]],[[0,0],[0,0]],[[-19656,-26],[-26,0]],[[0,0],[0,0]],[[-13364,-208],[-208,0]],[[0,0],[0,0]],[[-4342,-572],[-572,0]],[[0,0],[0,0]],[[-78,-624],[-624,0]],[[0,0],[0,0]],[[234,-234],[-234,0]],[[0],[0,0]],[[0],[0,-26]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
