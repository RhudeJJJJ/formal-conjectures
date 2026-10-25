/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode100
import Proofs.RadenkovicGutmanD39Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1521]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-13689],[0,-27378,45162],[-13689,45162,78]],[[0,0,0],[0,0,0],[0,0]],[[-123201,-455949,164619],[-455949,871182,151476],[164619,151476]],[[0,0,0],[0,0,0],[0,0]],[[-5641974,1212003,1380717],[1212003,6116058,165516],[1380717,165516]],[[0,0,0],[0,0,0],[0,0]],[[-29691441,32684769,3909906],[32684769,16309410,69264],[3909906,69264]],[[0,0,0],[0,0,0],[0,0]],[[42809364,160817280,5713188],[160817280,22953060,10218],[5713188,10218]],[[0,0,0],[0,0,0],[0,0]],[[920677797,412192989,4831164],[412192989,18873036,156],[4831164,156]],[[0,0,0],[0,0],[0]],[[4137076476,660867675,2445339],[660867675,9345258],[2445339]],[[0,0,0],[0,0],[0]],[[10684019190,713042616,731406],[713042616,2747082],[731406]],[[0,0,0],[0,0],[0]],[[18648275802,535515357,120159],[535515357,445458],[120159]],[[0,0,0],[0,0],[0]],[[23475717720,283513971,8697],[283513971,32058],[8697]],[[0,0,0],[0,0],[0]],[[22026735744,105457014,78],[105457014,312],[78]],[[0,0],[0]],[[15672784530,27000675],[27000675]],[[0,0],[0]],[[8520728190,4545567],[4545567]],[[0,0],[0]],[[3538821117,457509],[457509]],[[0,0],[0]],[[1114028916,21840],[21840]],[[0,0],[0]],[[261325818,156],[156]],[[0]],[[44310630]],[[0]],[[5149599]],[[0]],[[371046]],[[0]],[[13143]],[[0]],[[78]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
