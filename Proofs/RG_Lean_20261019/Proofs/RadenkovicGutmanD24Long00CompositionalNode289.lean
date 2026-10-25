/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[2304],[0],[0]],[[0,0],[0,0],[0]],[[69120,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[951552,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7967232,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[45338112,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[185624064,2304,0],[2304,0],[0]],[[0,0,0],[0,0],[0]],[[564671232,50688,0],[50688,0],[0]],[[0,0,0],[0,0],[0]],[[1299737088,495360,0],[495360,0],[0]],[[0,0,0],[0,0],[0]],[[2284005888,2833920,0],[2833920,0],[0]],[[0,0,0],[0,0],[0]],[[3069577728,10531584,0],[10531584,0],[0]],[[0,0,0],[0,0],[0]],[[3139640064,26680320,576],[26680320,1152],[576]],[[0,0,0],[0,0],[0]],[[2414458368,47061504,8064],[47061504,16128],[8064]],[[0,0,0],[0,0],[0]],[[1366212096,58014720,46656],[58014720,93312],[46656]],[[0,0,0],[0,0],[0]],[[548798976,49423104,144000],[49423104,288000],[144000]],[[0,0,0],[0,0],[0]],[[147246336,28270080,255744],[28270080,511488],[255744]],[[0,0,0],[0,0],[0]],[[23514624,10264320,263808],[10264320,527616],[263808]],[[0,0,0],[0,0],[0]],[[1679616,2115072,152640],[2115072,305280],[152640]],[[0,0,0],[0,0],[0]],[[0,186624,44928],[186624,89856],[44928]],[[0,0,0],[0,0],[0]],[[0,0,5184],[0,10368],[5184]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
