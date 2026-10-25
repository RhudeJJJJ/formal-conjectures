/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode100
import Proofs.RadenkovicGutmanD7Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,49]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-441],[0,-882,1386],[-441,1386,14]],[[0,0,0],[0,0,0],[0,0]],[[-3969,-15309,4683],[-15309,25998,4788],[4683,4788]],[[0,0,0],[0,0,0],[0,0]],[[-190134,17955,41069],[17955,186970,5516],[41069,5516]],[[0,0,0],[0,0,0],[0,0]],[[-1150065,905121,118930],[905121,509474,2576],[118930,2576]],[[0,0,0],[0,0,0],[0,0]],[[-163884,4701312,177828],[4701312,735588,490],[177828,490]],[[0,0,0],[0,0,0],[0,0]],[[23155685,12410909,154812],[12410909,625100,28],[154812,28]],[[0,0,0],[0,0],[0]],[[116364220,20386331,81627],[20386331,323946],[81627]],[[0,0,0],[0,0],[0]],[[315218806,22523704,25998],[22523704,101962],[25998]],[[0,0,0],[0,0],[0]],[[567690074,17354141,4767],[17354141,18578],[4767]],[[0,0,0],[0,0],[0]],[[732802392,9463475,441],[9463475,1722],[441]],[[0,0,0],[0,0],[0]],[[703305344,3650934,14],[3650934,56],[14]],[[0,0],[0]],[[511622930,981155],[981155]],[[0,0],[0]],[[284645886,177247],[177247]],[[0,0],[0]],[[121272893,20069],[20069]],[[0,0],[0]],[[39332916,1232],[1232]],[[0,0],[0]],[[9575034,28],[28]],[[0]],[[1705830]],[[0]],[[213087]],[[0]],[[17318]],[[0]],[[791]],[[0]],[[14]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
