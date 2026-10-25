/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode159
import Proofs.RadenkovicGutmanD38Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-540,0],[0,0]],[[0,0],[0,0]],[[-3384,0],[0,0]],[[0,0],[0,0]],[[-11484,0],[0,0]],[[0,0],[0,0]],[[-22896,0],[0,0]],[[0,0],[0,0]],[[-27216,-36],[-36,0]],[[0,0],[0,0]],[[-18504,-288],[-288,0]],[[0,0],[0,0]],[[-6012,-792],[-792,0]],[[0,0],[0,0]],[[-108,-864],[-864,0]],[[0,0],[0,0]],[[324,-324],[-324,0]],[[0],[0,0]],[[0],[0,-36]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
