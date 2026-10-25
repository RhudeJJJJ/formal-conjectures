/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode037
import Proofs.RadenkovicGutmanD38Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-540,0],[0,0]],[[0,0],[0,0]],[[-3384,0],[0,0]],[[0,0],[0,0]],[[-11484,0],[0,0]],[[0,0],[0,0]],[[-22896,0],[0,0]],[[0,0],[0,0]],[[-27216,-36],[-36,0]],[[0,0],[0,0]],[[-18504,-288],[-288,0]],[[0,0],[0,0]],[[-6012,-792],[-792,0]],[[0,0],[0,0]],[[-108,-864],[-864,0]],[[0,0],[0,0]],[[324,-324],[-324,0]],[[0],[0,0]],[[0],[0,-36]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
