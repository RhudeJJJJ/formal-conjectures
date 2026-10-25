/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode028
import Proofs.RadenkovicGutmanD31Long00CompositionalNode055
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e056 : NestedArithmetic.Expr 3 := .plus e028 e055
noncomputable def p056 : NestedHorner.Poly 3 := [[[],[]],[[0,3],[3]],[[0,0],[0]],[[45,13],[13]],[[0,0],[0]],[[300,16],[16]],[[0,0],[0]],[[779,7],[7]],[[0,0],[0]],[[1056,1],[1]],[[0]],[[828]],[[0]],[[388]],[[0]],[[107]],[[0]],[[16]],[[0]],[[1]]]
theorem step056 : p056=NestedHorner.add p028 p055 := by decide +kernel
#print axioms step056
theorem h056 : NestedArithmetic.compile e056=p056 := StagedExprCompile.compile_plus e056 e028 e055 p028 p055 p056 rfl h028 h055 step056
#print axioms h056
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
