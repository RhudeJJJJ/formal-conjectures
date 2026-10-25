/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode043
import Proofs.RadenkovicGutmanD45Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-18225],[0,-36450,11610],[-18225,11610]],[[0,0,0],[0,0,0],[0,0]],[[0,-715635,-53460],[-715635,67230,50310],[-53460,50310]],[[0,0,0],[0,0,0],[0,0]],[[-6633900,-5701995,194805],[-5701995,1550610,61920],[194805,61920]],[[0,0,0],[0,0,0],[0,0]],[[-79412400,-16672635,1092690],[-16672635,5200110,27090],[1092690,27090]],[[0,0,0],[0,0,0],[0,0]],[[-419760630,-16041420,2030490],[-16041420,8147700,3870],[2030490,3870]],[[0,0,0],[0,0],[0]],[[-1289623950,27454545,1955070],[27454545,7114500],[1955070]],[[0,0,0],[0,0],[0]],[[-2529423270,106808265,1070505],[106808265,3642570],[1070505]],[[0,0,0],[0,0],[0]],[[-3216950280,160660800,335430],[160660800,1084950],[335430]],[[0,0,0],[0,0],[0]],[[-2415580110,145581795,56025],[145581795,173970],[56025]],[[0,0,0],[0,0],[0]],[[-418188780,87155865,3870],[87155865,11610],[3870]],[[0,0],[0]],[[1369786680,35329410],[35329410]],[[0,0],[0]],[[1928082150,9612675],[9612675]],[[0,0],[0]],[[1458156870,1683405],[1683405]],[[0,0],[0]],[[743658570,171585],[171585]],[[0,0],[0]],[[269820450,7740],[7740]],[[0]],[[70175700]],[[0]],[[12833550]],[[0]],[[1570320]],[[0]],[[115560]],[[0]],[[3870]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
