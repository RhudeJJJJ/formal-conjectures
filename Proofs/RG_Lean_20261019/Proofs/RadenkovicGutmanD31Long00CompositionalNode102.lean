/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode100
import Proofs.RadenkovicGutmanD31Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,961]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-8649],[0,-17298,28458],[-8649,28458,62]],[[0,0,0],[0,0,0],[0,0]],[[-77841,-288765,103323],[-288765,548142,95604],[103323,95604]],[[0,0,0],[0,0,0],[0,0]],[[-3573990,742419,868589],[742419,3853114,104780],[868589,104780]],[[0,0,0],[0,0,0],[0,0]],[[-18973953,20487249,2462578],[20487249,10286978,44144],[2462578,44144]],[[0,0,0],[0,0,0],[0,0]],[[25339524,101076864,3602820],[101076864,14497956,6634],[3602820,6634]],[[0,0,0],[0,0,0],[0,0]],[[574502261,259471085,3051516],[259471085,11943308,124],[3051516,124]],[[0,0,0],[0,0],[0]],[[2595165868,416549387,1548171],[416549387,5929866],[1548171]],[[0,0,0],[0,0],[0]],[[6718311382,450020056,464814],[450020056,1750570],[464814]],[[0,0,0],[0,0],[0]],[[11745755354,338463053,76911],[338463053,286130],[76911]],[[0,0,0],[0,0],[0]],[[14806456344,179495363,5673],[179495363,21018],[5673]],[[0,0,0],[0,0],[0]],[[13909982720,66910710,62],[66910710,248],[62]],[[0,0],[0]],[[9909830450,17182835],[17182835]],[[0,0],[0]],[[5394808542,2906095],[2906095]],[[0,0],[0]],[[2243948237,294965],[294965]],[[0,0],[0]],[[707679780,14384],[14384]],[[0,0],[0]],[[166391322,124],[124]],[[0]],[[28304550]],[[0]],[[3305871]],[[0]],[[240374]],[[0]],[[8711]],[[0]],[[62]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
