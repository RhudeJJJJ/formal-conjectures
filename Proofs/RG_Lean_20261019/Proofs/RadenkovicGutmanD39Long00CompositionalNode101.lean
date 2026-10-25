/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode051
import Proofs.RadenkovicGutmanD39Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1521]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,36504],[0,36504,78]],[[0,0,0],[0,0,0],[0,0]],[[-123201,82134,205335],[82134,822744,113958],[205335,113958]],[[0,0,0],[0,0,0],[0,0]],[[-650754,5515614,1238328],[5515614,4965480,119340],[1238328,119340]],[[0,0,0],[0,0,0],[0,0]],[[30161079,45375876,3100032],[45375876,12441468,49062],[3100032,49062]],[[0,0,0],[0,0,0],[0,0]],[[359886618,173514276,4203810],[173514276,16886688,7332],[4203810,7332]],[[0,0,0],[0,0,0],[0,0]],[[1897790427,393047460,3375918],[393047460,13572936,156],[3375918,156]],[[0,0,0],[0,0],[0]],[[6062357418,582828402,1647906],[582828402,6630624],[1647906]],[[0,0,0],[0,0],[0]],[[13152919182,594580584,481416],[594580584,1938300],[481416]],[[0,0,0],[0,0],[0]],[[20541538680,427736634,78390],[427736634,315744],[78390]],[[0,0,0],[0,0],[0]],[[23878066524,218837658,5811],[218837658,23400],[5811]],[[0,0,0],[0,0],[0]],[[21072855336,79198548,78],[79198548,312],[78]],[[0,0],[0]],[[14273479740,19847880],[19847880]],[[0,0],[0]],[[7450053000,3291834],[3291834]],[[0,0],[0]],[[2989728651,329628],[329628]],[[0,0],[0]],[[914145882,16068],[16068]],[[0,0],[0]],[[209225718,156],[156]],[[0]],[[34767720]],[[0]],[[3980535]],[[0]],[[284934]],[[0]],[[10257]],[[0]],[[78]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
