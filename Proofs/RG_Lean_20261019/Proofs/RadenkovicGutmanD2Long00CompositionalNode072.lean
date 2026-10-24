/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode063
import Proofs.RadenkovicGutmanD2Long00CompositionalNode055
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e072 : NestedArithmetic.Expr 3 := .times e063 e055
noncomputable def p072 : NestedHorner.Poly 3 := [[[0],[0]],[[0,6],[6]],[[0,0],[0]],[[90,26],[26]],[[0,0],[0]],[[600,32],[32]],[[0,0],[0]],[[1558,14],[14]],[[0,0],[0]],[[2112,2],[2]],[[0]],[[1656]],[[0]],[[776]],[[0]],[[214]],[[0]],[[32]],[[0]],[[2]]]
theorem step072 : p072=NestedArithmetic.mul p063 p055 := by decide +kernel
#print axioms step072
theorem h072 : NestedArithmetic.compile e072=p072 := StagedExprCompile.compile_times e072 e063 e055 p063 p055 p072 rfl h063 h055 step072
#print axioms h072
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
