/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,784]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-14112,14112],[0,14112]],[[0,0,0],[0,0,0],[0,0]],[[63504,-127008,63504],[-127008,131712,37632],[63504,37632]],[[0,0,0],[0,0,0],[0,0]],[[-42336,-296352,338688],[-296352,939232,34496],[338688,34496]],[[0,0,0],[0,0,0],[0,0]],[[-2349648,2159136,762048],[2159136,2330048,12544],[762048,12544]],[[0,0,0],[0,0,0],[0,0]],[[-6468000,13528704,940800],[13528704,3067008,1568],[940800,1568]],[[0,0,0],[0,0],[0]],[[13614160,35795872,694624],[35795872,2386496],[694624]],[[0,0,0],[0,0],[0]],[[129174976,57255520,313600],[57255520,1127392],[313600]],[[0,0,0],[0,0],[0]],[[403582816,61224128,84672],[61224128,316736],[84672]],[[0,0,0],[0,0],[0]],[[776014176,45559808,12544],[45559808,48608],[12544]],[[0,0,0],[0,0],[0]],[[1044432256,23916704,784],[23916704,3136],[784]],[[0,0],[0]],[[1035689088,8820000],[8820000]],[[0,0],[0]],[[774962048,2234400],[2234400]],[[0,0],[0]],[[441901600,370048],[370048]],[[0,0],[0]],[[192109008,36064],[36064]],[[0,0],[0]],[[63162176,1568],[1568]],[[0]],[[15427552]],[[0]],[[2711072]],[[0]],[[323792]],[[0]],[[23520]],[[0]],[[784]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
