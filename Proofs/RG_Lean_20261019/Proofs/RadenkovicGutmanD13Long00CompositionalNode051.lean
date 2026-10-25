/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode049
import Proofs.RadenkovicGutmanD13Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,13]],[[0,0],[0,0]],[[-117,195],[195,2]],[[0,0],[0]],[[1461,668],[668]],[[0,0],[0]],[[12317,750],[750]],[[0,0],[0]],[[35220,330],[330]],[[0,0],[0]],[[52052,55],[55]],[[0,0],[0]],[[44628,2],[2]],[[0]],[[23007]],[[0]],[[7072]],[[0]],[[1219]],[[0]],[[99]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
