/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode075
import Proofs.RadenkovicGutmanD32Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1024]],[[0,0],[0,0,0],[0,0]],[[0,0,9216],[0,18432,18432],[9216,18432]],[[0,0,0],[0,0,0],[0,0]],[[-82944,304128,162816],[304128,491520,49152],[162816,49152]],[[0,0,0],[0,0,0],[0,0]],[[1050624,4893696,713728],[4893696,2312192,45056],[713728,45056]],[[0,0,0],[0,0,0],[0,0]],[[29611008,28191744,1464320],[28191744,4919296,16384],[1464320,16384]],[[0,0,0],[0,0,0],[0,0]],[[228194304,86779904,1683456],[86779904,5824512,2048],[1683456,2048]],[[0,0,0],[0,0],[0]],[[949492736,166177792,1163264],[166177792,4141056],[1163264]],[[0,0,0],[0,0],[0]],[[2545971200,213326848,492544],[213326848,1804288],[492544]],[[0,0,0],[0,0],[0]],[[4777666560,191057920,124928],[191057920,471040],[124928]],[[0,0,0],[0,0],[0]],[[6571436032,121785344,17408],[121785344,67584],[17408]],[[0,0,0],[0,0],[0]],[[6811822080,55559168,1024],[55559168,4096],[1024]],[[0,0],[0]],[[5410672640,17997824],[17997824]],[[0,0],[0]],[[3322398720,4039680],[4039680]],[[0,0],[0]],[[1580992512,596992],[596992]],[[0,0],[0]],[[580914176,52224],[52224]],[[0,0],[0]],[[163098624,2048],[2048]],[[0]],[[34314240]],[[0]],[[5232640]],[[0]],[[545792]],[[0]],[[34816]],[[0]],[[1024]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
