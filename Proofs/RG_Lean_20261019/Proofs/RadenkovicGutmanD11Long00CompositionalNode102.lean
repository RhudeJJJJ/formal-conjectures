/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode100
import Proofs.RadenkovicGutmanD11Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-1089],[0,-2178,3498],[-1089,3498,22]],[[0,0,0],[0,0,0],[0,0]],[[-9801,-37125,12243],[-37125,66462,11924],[12243,11924]],[[0,0,0],[0,0,0],[0,0]],[[-460350,67419,105149],[67419,472714,13420],[105149,13420]],[[0,0,0],[0,0,0],[0,0]],[[-2628153,2396889,301378],[2396889,1275538,5984],[301378,5984]],[[0,0,0],[0,0,0],[0,0]],[[1283964,12134144,445940],[12134144,1820676,1034],[445940,1034]],[[0,0,0],[0,0,0],[0,0]],[[64298861,31597445,383196],[31597445,1524908,44],[383196,44]],[[0,0,0],[0,0],[0]],[[305859268,51331027,198451],[51331027,774906],[198451]],[[0,0,0],[0,0],[0]],[[810106022,56109416,61534],[56109416,237050],[61534]],[[0,0,0],[0,0],[0]],[[1438045114,42742293,10791],[42742293,41250],[10791]],[[0,0,0],[0,0],[0]],[[1835272824,23007963,913],[23007963,3498],[913]],[[0,0,0],[0,0],[0]],[[1743628480,8738070,22],[8738070,88],[22]],[[0,0],[0]],[[1256047650,2301035],[2301035]],[[0,0],[0]],[[691798382,403975],[403975]],[[0,0],[0]],[[291516357,43725],[43725]],[[0,0],[0]],[[93359420,2464],[2464]],[[0,0],[0]],[[22379082,44],[44]],[[0]],[[3907750]],[[0]],[[474551]],[[0]],[[36894]],[[0]],[[1551]],[[0]],[[22]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
