/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode073
import Proofs.RadenkovicGutmanD2Long00CompositionalNode075
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .plus e073 e075
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0]],[[0,0,36],[0,72,72],[36,72]],[[0,0,0],[0,0,0],[0,0]],[[-324,1188,636],[1188,1920,192],[636,192]],[[0,0,0],[0,0,0],[0,0]],[[4104,19116,2788],[19116,9032,176],[2788,176]],[[0,0,0],[0,0,0],[0,0]],[[115668,110124,5720],[110124,19216,64],[5720,64]],[[0,0,0],[0,0,0],[0,0]],[[891384,338984,6576],[338984,22752,8],[6576,8]],[[0,0,0],[0,0],[0]],[[3708956,649132,4544],[649132,16176],[4544]],[[0,0,0],[0,0],[0]],[[9945200,833308,1924],[833308,7048],[1924]],[[0,0,0],[0,0],[0]],[[18662760,746320,488],[746320,1840],[488]],[[0,0,0],[0,0],[0]],[[25669672,475724,68],[475724,264],[68]],[[0,0,0],[0,0],[0]],[[26608680,217028,4],[217028,16],[4]],[[0,0],[0]],[[21135440,70304],[70304]],[[0,0],[0]],[[12978120,15780],[15780]],[[0,0],[0]],[[6175752,2332],[2332]],[[0,0],[0]],[[2269196,204],[204]],[[0,0],[0]],[[637104,8],[8]],[[0]],[[134040]],[[0]],[[20440]],[[0]],[[2132]],[[0]],[[136]],[[0]],[[4]]]
theorem step076 : p076=NestedHorner.add p073 p075 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_plus e076 e073 e075 p073 p075 p076 rfl h073 h075 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
