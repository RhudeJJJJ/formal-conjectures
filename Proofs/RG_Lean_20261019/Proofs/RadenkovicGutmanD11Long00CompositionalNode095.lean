/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode093
import Proofs.RadenkovicGutmanD11Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-1089],[0,-2178,3498],[-1089,3498,22]],[[0,0,0],[0,0,0],[0,0]],[[-9801,-37125,12243],[-37125,65670,11924],[12243,11924]],[[0,0,0],[0,0,0],[0,0]],[[-467478,60291,105149],[60291,465850,13420],[105149,13420]],[[0,0,0],[0,0,0],[0,0]],[[-2815857,2316105,301378],[2316105,1252218,5984],[301378,5984]],[[0,0,0],[0,0,0],[0,0]],[[-569316,11742104,445940],[11742104,1780372,1034],[445940,1034]],[[0,0,0],[0,0,0],[0,0]],[[54311477,30517685,383196],[30517685,1485836,44],[383196,44]],[[0,0,0],[0,0],[0]],[[271727676,49443339,198451],[49443339,752906],[198451]],[[0,0,0],[0,0],[0]],[[730071958,53893576,61534],[53893576,229922],[61534]],[[0,0,0],[0,0],[0]],[[1303098522,40944805,10791],[40944805,40018],[10791]],[[0,0,0],[0,0],[0]],[[1666771920,21988923,913],[21988923,3410],[913]],[[0,0,0],[0,0],[0]],[[1584916080,8335822,22],[8335822,88],[22]],[[0,0],[0]],[[1142079378,2192795],[2192795]],[[0,0],[0]],[[629150830,385055],[385055]],[[0,0],[0]],[[265210429,41789],[41789]],[[0,0],[0]],[[84998100,2376],[2376]],[[0,0],[0]],[[20403834,44],[44]],[[0]],[[3571942]],[[0]],[[435743]],[[0]],[[34166]],[[0]],[[1463]],[[0]],[[22]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
