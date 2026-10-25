/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode197
import Proofs.RadenkovicGutmanD26Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[160,0],[0,0]],[[0,0],[0,0]],[[2138,0],[0,0]],[[0,0],[0,0]],[[12858,0],[0,0]],[[0,0],[0,0]],[[42742,0],[0,0]],[[0,0],[0,0]],[[84192,2],[2,0]],[[0,0],[0,0]],[[99412,94],[94,0]],[[0,0],[0,0]],[[67986,616],[616,0]],[[0,0],[0,0]],[[24004,1452],[1452,0]],[[0,0],[0,0]],[[2868,1318],[1318,0]],[[0,0],[0,0]],[[-234,390],[390,2]],[[0],[0,0]],[[0],[0,26]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
