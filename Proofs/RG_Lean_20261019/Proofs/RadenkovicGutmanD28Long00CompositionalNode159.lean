/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode037
import Proofs.RadenkovicGutmanD28Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-390,0],[0,0]],[[0,0],[0,0]],[[-2444,0],[0,0]],[[0,0],[0,0]],[[-8294,0],[0,0]],[[0,0],[0,0]],[[-16536,0],[0,0]],[[0,0],[0,0]],[[-19656,-26],[-26,0]],[[0,0],[0,0]],[[-13364,-208],[-208,0]],[[0,0],[0,0]],[[-4342,-572],[-572,0]],[[0,0],[0,0]],[[-78,-624],[-624,0]],[[0,0],[0,0]],[[234,-234],[-234,0]],[[0],[0,0]],[[0],[0,-26]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
