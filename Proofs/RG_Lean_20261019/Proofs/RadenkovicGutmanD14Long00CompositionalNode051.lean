/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode049
import Proofs.RadenkovicGutmanD14Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,14]],[[0,0],[0,0]],[[-126,210],[210,2]],[[0,0],[0]],[[1572,718],[718]],[[0,0],[0]],[[13240,804],[804]],[[0,0],[0]],[[37822,352],[352]],[[0,0],[0]],[[55836,58],[58]],[[0,0],[0]],[[47808,2],[2]],[[0]],[[24602]],[[0]],[[7542]],[[0]],[[1294]],[[0]],[[104]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
