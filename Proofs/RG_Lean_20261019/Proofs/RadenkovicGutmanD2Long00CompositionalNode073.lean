/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode032
import Proofs.RadenkovicGutmanD2Long00CompositionalNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .times e032 e051
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,72],[0,72]],[[0,0,0],[0,0,0],[0,0]],[[-324,0,324],[0,1296,192],[324,192]],[[0,0,0],[0,0,0],[0,0]],[[-5616,5832,1728],[5832,6912,176],[1728,176]],[[0,0,0],[0,0,0],[0,0]],[[-17172,46656,3888],[46656,15552,64],[3888,64]],[[0,0,0],[0,0,0],[0,0]],[[81600,167184,4800],[167184,19200,8],[4800,8]],[[0,0,0],[0,0],[0]],[[777692,354240,3544],[354240,14176],[3544]],[[0,0,0],[0,0],[0]],[[2870816,493560,1600],[493560,6400],[1600]],[[0,0,0],[0,0],[0]],[[6558296,475776,432],[475776,1728],[432]],[[0,0,0],[0,0],[0]],[[10444048,325088,64],[325088,256],[64]],[[0,0,0],[0,0],[0]],[[12216848,158592,4],[158592,16],[4]],[[0,0],[0]],[[10784528,54840],[54840]],[[0,0],[0]],[[7284608,13120],[13120]],[[0,0],[0]],[[3784480,2064],[2064]],[[0,0],[0]],[[1509084,192],[192]],[[0,0],[0]],[[457536,8],[8]],[[0]],[[103512]],[[0]],[[16912]],[[0]],[[1884]],[[0]],[[128]],[[0]],[[4]]]
theorem step073 : p073=NestedArithmetic.mul p032 p051 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_times e073 e032 e051 p032 p051 p073 rfl h032 h051 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
