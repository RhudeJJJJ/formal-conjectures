/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode177
import Proofs.RadenkovicGutmanD2Long00CompositionalNode180
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e181 : NestedArithmetic.Expr 3 := .plus e177 e180
noncomputable def p181 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[16,0],[0]],[[0,0],[0]],[[107,0],[0]],[[0,0],[0]],[[388,0],[0]],[[0,0],[0]],[[828,0],[0]],[[0,0],[0]],[[1056,1],[1]],[[0,0],[0]],[[779,7],[7]],[[0,0],[0]],[[300,16],[16]],[[0,0],[0]],[[45,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step181 : p181=NestedHorner.add p177 p180 := by decide +kernel
#print axioms step181
theorem h181 : NestedArithmetic.compile e181=p181 := StagedExprCompile.compile_plus e181 e177 e180 p177 p180 p181 rfl h177 h180 step181
#print axioms h181
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
