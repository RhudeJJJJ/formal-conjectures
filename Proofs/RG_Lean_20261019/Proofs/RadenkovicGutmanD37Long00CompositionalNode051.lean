/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode049
import Proofs.RadenkovicGutmanD37Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,37]],[[0,0],[0,0]],[[-333,555],[555,2]],[[0,0],[0]],[[4125,1868],[1868]],[[0,0],[0]],[[34469,2046],[2046]],[[0,0],[0]],[[97668,858],[858]],[[0,0],[0]],[[142868,127],[127]],[[0,0],[0]],[[120948,2],[2]],[[0]],[[61287]],[[0]],[[18352]],[[0]],[[3019]],[[0]],[[219]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
