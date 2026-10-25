/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode045
import Proofs.RadenkovicGutmanD20Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,20]],[[0,0],[0,0]],[[-180,300],[300,2]],[[0,0],[0]],[[2202,1018],[1018]],[[0,0],[0]],[[18466,1128],[1128]],[[0,0],[0]],[[52374,484],[484]],[[0,0],[0]],[[76708,76],[76]],[[0,0],[0]],[[65112,2],[2]],[[0]],[[33172]],[[0]],[[10038]],[[0]],[[1688]],[[0]],[[130]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
