/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode202
import Proofs.RadenkovicGutmanD22Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[56,0],[0,0]],[[0,0],[0,0]],[[618,0],[0,0]],[[0,0],[0,0]],[[3646,0],[0,0]],[[0,0],[0,0]],[[12854,0],[0,0]],[[0,0],[0,0]],[[28280,2],[2,0]],[[0,0],[0,0]],[[39028,38],[38,0]],[[0,0],[0,0]],[[32854,220],[220,0]],[[0,0],[0,0]],[[15652,532],[532,0]],[[0,0],[0,0]],[[3516,546],[546,0]],[[0,0],[0,0]],[[198,198],[198,2]],[[0],[0,0]],[[0],[0,22]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
