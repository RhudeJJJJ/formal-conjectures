/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode033
import Proofs.RadenkovicGutmanD39Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1521]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,36504],[0,36504,78]],[[0,0,0],[0,0,0],[0,0]],[[-123201,-82134,205335],[-82134,793962,113958],[205335,113958]],[[0,0,0],[0,0,0],[0,0]],[[-3373812,3121092,1238328],[3121092,4716036,119340],[1238328,119340]],[[0,0,0],[0,0,0],[0,0]],[[-14441895,30558060,3100032],[30558060,11593998,49062],[3100032,49062]],[[0,0,0],[0,0,0],[0,0]],[[34964514,121972266,4203810],[121972266,15422004,7332],[4203810,7332]],[[0,0,0],[0,0,0],[0,0]],[[498272229,280307196,3375918],[280307196,12153024,156],[3375918,156]],[[0,0,0],[0,0],[0]],[[2062068996,418204332,1647906],[418204332,5831124],[1647906]],[[0,0,0],[0,0],[0]],[[5078192106,428465232,481416],[428465232,1679262],[481416]],[[0,0,0],[0,0],[0]],[[8587220304,309720762,78390],[309720762,270972],[78390]],[[0,0,0],[0,0],[0]],[[10581079938,159446118,5811],[159446118,20202],[5811]],[[0,0,0],[0,0],[0]],[[9791221908,58167954,78],[58167954,312],[78]],[[0,0],[0]],[[6911276736,14727960],[14727960]],[[0,0],[0]],[[3745274520,2476500],[2476500]],[[0,0],[0]],[[1556834721,253188],[253188]],[[0,0],[0]],[[492434748,12870],[12870]],[[0,0],[0]],[[116563122,156],[156]],[[0]],[[20057544]],[[0]],[[2387697]],[[0]],[[179712]],[[0]],[[7059]],[[0]],[[78]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
