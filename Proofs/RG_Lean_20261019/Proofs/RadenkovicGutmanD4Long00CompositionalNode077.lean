/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode074
import Proofs.RadenkovicGutmanD4Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .plus e074 e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0]],[[0,0,144],[0,288,288],[144,288]],[[0,0,0],[0,0,0],[0,0]],[[-1296,4752,2544],[4752,7680,768],[2544,768]],[[0,0,0],[0,0,0],[0,0]],[[16416,76464,11152],[76464,36128,704],[11152,704]],[[0,0,0],[0,0,0],[0,0]],[[462672,440496,22880],[440496,76864,256],[22880,256]],[[0,0,0],[0,0,0],[0,0]],[[3565536,1355936,26304],[1355936,91008,32],[26304,32]],[[0,0,0],[0,0],[0]],[[14835824,2596528,18176],[2596528,64704],[18176]],[[0,0,0],[0,0],[0]],[[39780800,3333232,7696],[3333232,28192],[7696]],[[0,0,0],[0,0],[0]],[[74651040,2985280,1952],[2985280,7360],[1952]],[[0,0,0],[0,0],[0]],[[102678688,1902896,272],[1902896,1056],[272]],[[0,0,0],[0,0],[0]],[[106434720,868112,16],[868112,64],[16]],[[0,0],[0]],[[84541760,281216],[281216]],[[0,0],[0]],[[51912480,63120],[63120]],[[0,0],[0]],[[24703008,9328],[9328]],[[0,0],[0]],[[9076784,816],[816]],[[0,0],[0]],[[2548416,32],[32]],[[0]],[[536160]],[[0]],[[81760]],[[0]],[[8528]],[[0]],[[544]],[[0]],[[16]]]
theorem step077 : p077=NestedHorner.add p074 p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_plus e077 e074 e076 p074 p076 p077 rfl h074 h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
