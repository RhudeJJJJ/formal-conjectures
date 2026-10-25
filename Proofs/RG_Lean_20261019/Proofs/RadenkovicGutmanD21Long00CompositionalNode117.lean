/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode112
import Proofs.RadenkovicGutmanD21Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,504],[0,504,1528]],[[0,0,0],[0,0,0],[0,0,0]],[[0,4536,20412],[4536,18432,30192],[20412,30192,4]],[[0,0,0],[0,0,0],[0,0]],[[246240,474336,297648],[474336,642792,78288],[297648,78288]],[[0,0,0],[0,0,0],[0,0]],[[7544124,7189992,1247328],[7189992,3128576,71288],[1247328,71288]],[[0,0,0],[0,0,0],[0,0]],[[88438176,41190720,2509728],[41190720,6824040,25968],[2509728,25968]],[[0,0,0],[0,0,0],[0,0]],[[540768180,127592904,2854728],[127592904,8303920,3288],[2854728,3288]],[[0,0,0],[0,0,0],[0,0]],[[2036596216,247189256,1960048],[247189256,6087744,8],[1960048,8]],[[0,0,0],[0,0],[0]],[[5186355092,322060312,827012],[322060312,2741104],[827012]],[[0,0,0],[0,0],[0]],[[9447205952,293362368,209632],[293362368,740840],[209632]],[[0,0,0],[0,0],[0]],[[12754336544,190460352,29332],[190460352,110416],[29332]],[[0,0,0],[0,0],[0]],[[13056265112,88590120,1760],[88590120,7048],[1760]],[[0,0,0],[0,0],[0]],[[10278016848,29285872,4],[29285872,16],[4]],[[0,0],[0]],[[6268764528,6715352],[6715352]],[[0,0],[0]],[[2967607416,1015840],[1015840]],[[0,0],[0]],[[1086104232,91408],[91408]],[[0,0],[0]],[[304084084,3760],[3760]],[[0,0],[0]],[[63879264,8],[8]],[[0]],[[9743248]],[[0]],[[1019496]],[[0]],[[65676]],[[0]],[[2000]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
