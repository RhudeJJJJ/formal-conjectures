/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode048
import Proofs.RadenkovicGutmanD4Long00CompositionalNode049
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e050 : NestedArithmetic.Expr 3 := .plus e048 e049
noncomputable def p050 : NestedHorner.Poly 3 := [[[0],[0,4]],[[0,0],[0,0]],[[-36,60],[60,2]],[[0,0],[0]],[[462,218],[218]],[[0,0],[0]],[[4010,264],[264]],[[0,0],[0]],[[11802,132],[132]],[[0,0],[0]],[[17996,28],[28]],[[0,0],[0]],[[16008,2],[2]],[[0]],[[8652]],[[0]],[[2842]],[[0]],[[544]],[[0]],[[54]],[[0]],[[2]]]
theorem step050 : p050=NestedHorner.add p048 p049 := by decide +kernel
#print axioms step050
theorem h050 : NestedArithmetic.compile e050=p050 := StagedExprCompile.compile_plus e050 e048 e049 p048 p049 p050 rfl h048 h049 step050
#print axioms h050
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
