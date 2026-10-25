/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode191
import Proofs.RadenkovicGutmanD20Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[50,0],[0,0]],[[0,0],[0,0]],[[488,0],[0,0]],[[0,0],[0,0]],[[2518,0],[0,0]],[[0,0],[0,0]],[[7652,0],[0,0]],[[0,0],[0,0]],[[14232,2],[2,0]],[[0,0],[0,0]],[[16148,36],[36,0]],[[0,0],[0,0]],[[10614,204],[204,0]],[[0,0],[0,0]],[[3346,488],[488,0]],[[0,0],[0,0]],[[42,498],[498,0]],[[0,0],[0,0]],[[-180,180],[180,2]],[[0],[0,0]],[[0],[0,20]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
