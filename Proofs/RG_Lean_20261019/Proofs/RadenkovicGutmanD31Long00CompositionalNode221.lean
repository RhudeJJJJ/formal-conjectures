/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[1922],[0],[0]],[[0,0],[0,0],[0]],[[59582,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[847602,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[7334352,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[43141212,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[182616908,2883,0],[2883,0],[0]],[[0,0,0],[0,0],[0]],[[574503098,64387,0],[64387,0],[0]],[[0,0,0],[0,0],[0]],[[1367866258,639065,0],[639065,0],[0]],[[0,0,0],[0,0],[0]],[[2486806608,3715226,0],[3715226,0],[0]],[[0,0,0],[0,0],[0]],[[3457637638,14039249,0],[14039249,0],[0]],[[0,0,0],[0,0],[0]],[[3657956166,36190299,961],[36190299,1922],[961]],[[0,0,0],[0,0],[0]],[[2908097476,64998196,13454],[64998196,26908],[13454]],[[0,0,0],[0,0],[0]],[[1699620756,81624457,77841],[81624457,155682],[77841]],[[0,0,0],[0,0],[0]],[[704236176,70847803,240250],[70847803,480500],[240250]],[[0,0,0],[0,0],[0]],[[194550606,41274950,426684],[41274950,853368],[426684]],[[0,0,0],[0,0],[0]],[[31914810,15248187,440138],[15248187,880276],[440138]],[[0,0,0],[0,0],[0]],[[2335230,3191481,254665],[3191481,509330],[254665]],[[0,0,0],[0,0],[0]],[[0,285417,74958],[285417,149916],[74958]],[[0,0,0],[0,0],[0]],[[0,0,8649],[0,17298],[8649]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
