/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode096
import Proofs.RadenkovicGutmanD44Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,11616],[0,11616,-3696]],[[0,0,0],[0,0,0],[0,0]],[[0,0,139392],[0,473616,-15928],[139392,-15928]],[[0,0,0],[0,0,0],[0,0]],[[484704,3846744,736824],[3846744,2218920,-114312],[736824,-114312]],[[0,0,0],[0,0,0],[0,0]],[[33627528,33389928,1467224],[33389928,3390112,-134112],[1467224,-134112]],[[0,0,0],[0,0,0],[0,0]],[[362869848,126143424,1157904],[126143424,336072,-54648],[1157904,-54648]],[[0,0,0],[0,0,0],[0,0]],[[1891210992,270604136,-186824],[270604136,-4929232,-7304],[-186824,-7304]],[[0,0,0],[0,0],[0]],[[6014492264,359208080,-1015520],[359208080,-6433152],[-1015520]],[[0,0,0],[0,0],[0]],[[12889921000,297001144,-772728],[297001144,-3868480],[-772728]],[[0,0,0],[0,0],[0]],[[19587912080,136973936,-278608],[136973936,-1252152],[-278608]],[[0,0,0],[0,0],[0]],[[21664211536,10921768,-50072],[10921768,-210848],[-50072]],[[0,0,0],[0,0],[0]],[[17591730376,-28542008,-3608],[-28542008,-14520],[-3608]],[[0,0],[0]],[[10388349312,-19923024],[-19923024]],[[0,0],[0]],[[4279606144,-6862064],[-6862064]],[[0,0],[0]],[[1066565808,-1370160],[-1370160]],[[0,0],[0]],[[41782136,-151536],[-151536]],[[0,0],[0]],[[-85614936,-7216],[-7216]],[[0]],[[-38412880]],[[0]],[[-8970544]],[[0]],[[-1261832]],[[0]],[[-101464]],[[0]],[[-3608]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
