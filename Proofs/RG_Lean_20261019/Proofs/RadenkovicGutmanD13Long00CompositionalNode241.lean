/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode240
import Proofs.RadenkovicGutmanD13Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e241 : NestedArithmetic.Expr 3 := .times e240 e001
noncomputable def p241 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[169,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5577,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[84669,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[784160,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4953390,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[22604933,169,0],[169,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[77014483,4056,0],[4056,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[199651192,43433,0],[43433,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[397787130,273780,0],[273780,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[611126646,1128751,0],[1128751,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[722126691,3199170,0],[3199170,169,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[650838604,6379412,0],[6379412,2366,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[440713806,9010404,0],[9010404,13689,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[218876801,8959873,0],[8959873,42250,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[76767405,6157008,0],[6157008,75036,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[17868708,2824835,0],[2824835,77402,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2459457,815256,0],[815256,44785,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[150579,132327,0],[132327,13182,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,9126,0],[9126,1521,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step241 : p241=NestedArithmetic.mul p240 p001 := by decide +kernel
#print axioms step241
theorem h241 : NestedArithmetic.compile e241=p241 := StagedExprCompile.compile_times e241 e240 e001 p240 p001 p241 rfl h240 h001 step241
#print axioms h241
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
