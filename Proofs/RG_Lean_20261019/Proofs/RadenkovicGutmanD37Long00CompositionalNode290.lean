/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode289
import Proofs.RadenkovicGutmanD37Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[5476,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[164280,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2261588,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[18936008,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[107756728,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[441179416,5476,0],[5476,0],[0]],[[0,0,0],[0,0],[0]],[[1342074508,120472,0],[120472,0],[0]],[[0,0,0],[0,0],[0]],[[3089132072,1177340,0],[1177340,0],[0]],[[0,0,0],[0,0],[0]],[[5428479272,6735480,0],[6735480,0],[0]],[[0,0,0],[0,0],[0]],[[7295576232,25030796,0],[25030796,0],[0]],[[0,0,0],[0,0],[0]],[[7462095916,63412080,1369],[63412080,2738],[1369]],[[0,0,0],[0,0],[0]],[[5738530392,111852776,19166],[111852776,38332],[19166]],[[0,0,0],[0,0],[0]],[[3247125624,137885680,110889],[137885680,221778],[110889]],[[0,0,0],[0,0],[0]],[[1304350344,117465676,342250],[117465676,684500],[342250]],[[0,0,0],[0,0],[0]],[[349965684,67190520,607836],[67190520,1215672],[607836]],[[0,0,0],[0,0],[0]],[[55888056,24395580,627002],[24395580,1254004],[627002]],[[0,0,0],[0,0],[0]],[[3992004,5026968,362785],[5026968,725570],[362785]],[[0,0,0],[0,0],[0]],[[0,443556,106782],[443556,213564],[106782]],[[0,0,0],[0,0],[0]],[[0,0,12321],[0,24642],[12321]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
