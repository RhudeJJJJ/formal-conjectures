/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode221
import Proofs.RadenkovicGutmanD24Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[1152,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[35712,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[508032,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[4396032,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[25857792,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[109456128,1728,0],[1728,0],[0]],[[0,0,0],[0,0],[0]],[[344343168,38592,0],[38592,0],[0]],[[0,0,0],[0,0],[0]],[[819865728,383040,0],[383040,0],[0]],[[0,0,0],[0,0],[0]],[[1490531328,2226816,0],[2226816,0],[0]],[[0,0,0],[0,0],[0]],[[2072423808,8414784,0],[8414784,0],[0]],[[0,0,0],[0,0],[0]],[[2192489856,21691584,576],[21691584,1152],[576]],[[0,0,0],[0,0],[0]],[[1743042816,38958336,8064],[38958336,16128],[8064]],[[0,0,0],[0,0],[0]],[[1018711296,48923712,46656],[48923712,93312],[46656]],[[0,0,0],[0,0],[0]],[[422102016,42464448,144000],[42464448,288000],[144000]],[[0,0,0],[0,0],[0]],[[116608896,24739200,255744],[24739200,511488],[255744]],[[0,0,0],[0,0],[0]],[[19128960,9139392,263808],[9139392,527616],[263808]],[[0,0,0],[0,0],[0]],[[1399680,1912896,152640],[1912896,305280],[152640]],[[0,0,0],[0,0],[0]],[[0,171072,44928],[171072,89856],[44928]],[[0,0,0],[0,0],[0]],[[0,0,5184],[0,10368],[5184]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
