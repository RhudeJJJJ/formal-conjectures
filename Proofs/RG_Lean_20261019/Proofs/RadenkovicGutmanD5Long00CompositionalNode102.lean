/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode100
import Proofs.RadenkovicGutmanD5Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-225],[0,-450,690],[-225,690,10]],[[0,0,0],[0,0,0],[0,0]],[[-2025,-7965,2235],[-7965,12750,2420],[2235,2420]],[[0,0,0],[0,0,0],[0,0]],[[-99090,3915,20105],[3915,92890,2860],[20105,2860]],[[0,0,0],[0,0,0],[0,0]],[[-634905,425025,58930],[425025,255970,1400],[58930,1400]],[[0,0,0],[0,0,0],[0,0]],[[-467400,2279360,89180],[2279360,374340,290],[89180,290]],[[0,0,0],[0,0,0],[0,0]],[[10196285,6116165,78780],[6116165,323180,20],[78780,20]],[[0,0,0],[0,0],[0]],[[55162480,10176355,42355],[10176355,170970],[42355]],[[0,0,0],[0,0],[0]],[[153619430,11380400,13870],[11380400,55370],[13870]],[[0,0,0],[0,0],[0]],[[281410930,8879565,2655],[8879565,10530],[2655]],[[0,0,0],[0,0],[0]],[[368037960,4910355,265],[4910355,1050],[265]],[[0,0,0],[0,0],[0]],[[357262240,1925790,10],[1925790,40],[10]],[[0,0],[0]],[[262702050,528275],[528275]],[[0,0],[0]],[[147750830,98095],[98095]],[[0,0],[0]],[[63681525,11565],[11565]],[[0,0],[0]],[[20924360,760],[760]],[[0,0],[0]],[[5172810,20],[20]],[[0]],[[939550]],[[0]],[[120455]],[[0]],[[10170]],[[0]],[[495]],[[0]],[[10]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
