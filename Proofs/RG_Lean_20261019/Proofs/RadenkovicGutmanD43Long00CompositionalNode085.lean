/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode073
import Proofs.RadenkovicGutmanD43Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-3096,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27864,-427248,0],[-427248,-94170,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7330554,-6113826,0],[-6113826,-674756,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-115062066,-37289772,0],[-37289772,-2140282,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-822846624,-128228150,0],[-128228150,-3579492,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3502779914,-277885436,0],[-277885436,-3408008,0],[0,0]],[[0,0,0],[0,0],[0]],[[-9924990390,-402620438,0],[-402620438,-1898364],[0]],[[0,0,0],[0,0],[0]],[[-19892830108,-403517160,0],[-403517160,-610858],[0]],[[0,0,0],[0,0],[0]],[[-29273418912,-284924364,0],[-284924364,-105092],[0]],[[0,0,0],[0,0],[0]],[[-32387749382,-142574584,0],[-142574584,-7482],[0]],[[0,0,0],[0,0],[0]],[[-27345544700,-50214110,0],[-50214110,0],[0]],[[0,0],[0]],[[-17764755980,-12161260],[-12161260]],[[0,0],[0]],[[-8901453736,-1926830],[-1926830]],[[0,0],[0]],[[-3428802198,-179740],[-179740]],[[0,0],[0]],[[-1005159486,-7482],[-7482]],[[0,0],[0]],[[-220019820,0],[0]],[[0]],[[-34797320]],[[0]],[[-3753986]],[[0]],[[-247078]],[[0]],[[-7482]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
