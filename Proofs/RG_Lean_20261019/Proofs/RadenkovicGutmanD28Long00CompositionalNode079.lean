/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode033
import Proofs.RadenkovicGutmanD28Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2352],[0,2352]],[[0,0,0],[0,0,0],[0,0]],[[0,-21168,21168],[-21168,77616,10192],[21168,10192]],[[0,0,0],[0,0,0],[0,0]],[[-317520,232848,148176],[232848,531552,12544],[148176,12544]],[[0,0,0],[0,0,0],[0,0]],[[-2010960,3273984,409248],[3273984,1429232,5488],[409248,5488]],[[0,0,0],[0,0,0],[0,0]],[[1100736,14816816,593488],[14816816,2014880,784],[593488,784]],[[0,0,0],[0,0],[0]],[[51793392,36686496,498624],[36686496,1646400],[498624]],[[0,0,0],[0,0],[0]],[[246198736,57632624,250096],[57632624,804384],[250096]],[[0,0,0],[0,0],[0]],[[651637280,61319776,73696],[61319776,231280],[73696]],[[0,0,0],[0,0],[0]],[[1156666560,45573136,11760],[45573136,36064],[11760]],[[0,0,0],[0,0],[0]],[[1477271600,23917488,784],[23917488,2352],[784]],[[0,0],[0]],[[1405163200,8820000],[8820000]],[[0,0],[0]],[[1013119296,2234400],[2234400]],[[0,0],[0]],[[557762688,370048],[370048]],[[0,0],[0]],[[234325840,36064],[36064]],[[0,0],[0]],[[74490192,1568],[1568]],[[0]],[[17597664]],[[0]],[[2991744]],[[0]],[[345744]],[[0]],[[24304]],[[0]],[[784]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
