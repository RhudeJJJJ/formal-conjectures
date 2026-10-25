/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode051
import Proofs.RadenkovicGutmanD35Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1225]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,29400],[0,29400,70]],[[0,0,0],[0,0,0],[0,0]],[[-99225,66150,165375],[66150,662760,91910],[165375,91910]],[[0,0,0],[0,0,0],[0,0]],[[-523530,4443390,997920],[4443390,4002600,96460],[997920,96460]],[[0,0,0],[0,0,0],[0,0]],[[24312015,36568980,2499840],[36568980,10036460,39830],[2499840,39830]],[[0,0,0],[0,0,0],[0,0]],[[290121090,139894580,3392690],[139894580,13634880,6020],[3392690,6020]],[[0,0,0],[0,0,0],[0,0]],[[1530239795,317033220,2727550],[317033220,10972360,140],[2727550,140]],[[0,0,0],[0,0],[0]],[[4889534370,470348690,1333570],[470348690,5369280],[1333570]],[[0,0,0],[0,0],[0]],[[10611457150,480117400,390600],[480117400,1573740],[390600]],[[0,0,0],[0,0],[0]],[[16577764840,345642570,63910],[345642570,257600],[63910]],[[0,0,0],[0,0],[0]],[[19277424460,176999690,4795],[176999690,19320],[4795]],[[0,0,0],[0,0],[0]],[[17019716840,64136100,70],[64136100,280],[70]],[[0,0],[0]],[[11533687900,16101400],[16101400]],[[0,0],[0]],[[6023504200,2677850],[2677850]],[[0,0],[0]],[[2418986115,269500],[269500]],[[0,0],[0]],[[740317970,13300],[13300]],[[0,0],[0]],[[169652070,140],[140]],[[0]],[[28242200]],[[0]],[[3242575]],[[0]],[[233310]],[[0]],[[8505]],[[0]],[[70]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
