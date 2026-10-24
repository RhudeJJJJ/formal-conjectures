/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode044
import Proofs.RadenkovicGutmanD2Long00CompositionalNode046
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e047 : NestedArithmetic.Expr 3 := .plus e044 e046
noncomputable def p047 : NestedHorner.Poly 3 := [[[0],[0,2]],[[0,0],[0,0]],[[-18,30],[30,2]],[[0,0],[0]],[[204,118],[118]],[[0,0],[0]],[[1852,156],[156]],[[0,0],[0]],[[5538,88],[88]],[[0,0],[0]],[[8596,22],[22]],[[0,0],[0]],[[7872,2],[2]],[[0]],[[4462]],[[0]],[[1578]],[[0]],[[338]],[[0]],[[40]],[[0]],[[2]]]
theorem step047 : p047=NestedHorner.add p044 p046 := by decide +kernel
#print axioms step047
theorem h047 : NestedArithmetic.compile e047=p047 := StagedExprCompile.compile_plus e047 e044 e046 p044 p046 p047 rfl h044 h046 step047
#print axioms h047
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
