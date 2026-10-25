/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode093
import Proofs.RadenkovicGutmanD20Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,400]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-3600],[0,-7200,11760],[-3600,11760,40]],[[0,0,0],[0,0,0],[0,0]],[[-32400,-120960,42240],[-120960,224160,39680],[42240,39680]],[[0,0,0],[0,0,0],[0,0]],[[-1510920,270000,357320],[270000,1578880,43840],[357320,43840]],[[0,0,0],[0,0,0],[0,0]],[[-8478000,8197920,1016320],[8197920,4219680,18800],[1016320,18800]],[[0,0,0],[0,0,0],[0,0]],[[5271000,40766240,1491920],[40766240,5956480,2960],[1491920,2960]],[[0,0,0],[0,0,0],[0,0]],[[212930960,104964560,1269120],[104964560,4921280,80],[1269120,80]],[[0,0,0],[0,0],[0]],[[997237080,168832560,647920],[168832560,2456480],[647920]],[[0,0,0],[0,0],[0]],[[2615067040,182731600,196480],[182731600,732320],[196480]],[[0,0,0],[0,0],[0]],[[4602745680,137737600,33120],[137737600,122080],[33120]],[[0,0,0],[0,0],[0]],[[5827556160,73266720,2560],[73266720,9440],[2560]],[[0,0,0],[0,0],[0]],[[5493442560,27432400,40],[27432400,160],[40]],[[0,0],[0]],[[3925880160,7092800],[7092800]],[[0,0],[0]],[[2144128480,1213280],[1213280]],[[0,0],[0]],[[895156240,125840],[125840]],[[0,0],[0]],[[283612440,6480],[6480]],[[0,0],[0]],[[67094880,80],[80]],[[0]],[[11514640]],[[0]],[[1363760]],[[0]],[[101720]],[[0]],[[3920]],[[0]],[[40]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
