/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode048
import Proofs.RadenkovicGutmanD3Long00StagedUNode049
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e050 : NestedArithmetic.Expr 3 := .plus e048 e049
noncomputable def p050 : NestedHorner.Poly 3 := [[[0],[0,3]],[[0,0],[0,0]],[[-27,45],[45,2]],[[0,0],[0]],[[351,168],[168]],[[0,0],[0]],[[3087,210],[210]],[[0,0],[0]],[[9200,110],[110]],[[0,0],[0]],[[14212,25],[25]],[[0,0],[0]],[[12828,2],[2]],[[0]],[[7057]],[[0]],[[2372]],[[0]],[[469]],[[0]],[[49]],[[0]],[[2]]]
theorem step050 : p050=NestedHorner.add p048 p049 := by decide +kernel
#print axioms step050
theorem h050 : NestedArithmetic.compile e050=p050 := StagedExprCompile.compile_plus e050 e048 e049 p048 p049 p050 rfl h048 h049 step050
#print axioms h050
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
