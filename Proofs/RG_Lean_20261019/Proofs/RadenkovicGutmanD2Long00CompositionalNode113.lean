/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode111
import Proofs.RadenkovicGutmanD2Long00CompositionalNode112
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .plus e111 e112
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0]],[[0,0,36],[0,0,72],[36,72]],[[0,0,0],[0,0,0],[0,0]],[[324,648,636],[648,1296,192],[636,192]],[[0,0,0],[0,0,0],[0,0]],[[11448,13176,2788],[13176,6912,176],[2788,176]],[[0,0,0],[0,0,0],[0,0]],[[151308,82296,5720],[82296,15552,64],[5720,64]],[[0,0,0],[0,0,0],[0,0]],[[989544,265344,6576],[265344,19200,8],[6576,8]],[[0,0,0],[0,0],[0]],[[3880564,525848,4544],[525848,14176],[4544]],[[0,0,0],[0,0],[0]],[[10146640,695000,1924],[695000,6400],[1924]],[[0,0,0],[0,0],[0]],[[18826168,639184,488],[639184,1728],[488]],[[0,0,0],[0,0],[0]],[[25762312,417728,68],[417728,256],[68]],[[0,0,0],[0,0],[0]],[[26645248,195160,4],[195160,16],[4]],[[0,0],[0]],[[21145280,64680],[64680]],[[0,0],[0]],[[12979840,14840],[14840]],[[0,0],[0]],[[6175928,2240],[2240]],[[0,0],[0]],[[2269204,200],[200]],[[0,0],[0]],[[637104,8],[8]],[[0]],[[134040]],[[0]],[[20440]],[[0]],[[2132]],[[0]],[[136]],[[0]],[[4]]]
theorem step113 : p113=NestedHorner.add p111 p112 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_plus e113 e111 e112 p111 p112 p113 rfl h111 h112 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
