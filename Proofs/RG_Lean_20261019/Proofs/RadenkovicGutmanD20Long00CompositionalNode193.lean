/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode192
import Proofs.RadenkovicGutmanD20Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[50,0],[0,0]],[[0,0],[0,0]],[[488,0],[0,0]],[[0,0],[0,0]],[[2518,0],[0,0]],[[0,0],[0,0]],[[7652,0],[0,0]],[[0,0],[0,0]],[[14232,2],[2,0]],[[0,0],[0,0]],[[16148,36],[36,0]],[[0,0],[0,0]],[[10614,204],[204,0]],[[0,0],[0,0]],[[3346,488],[488,0]],[[0,0],[0,0]],[[42,498],[498,0]],[[0,0],[0,0]],[[-180,180],[180,2]],[[0],[0,0]],[[0],[0,20]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
