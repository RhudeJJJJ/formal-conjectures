/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,768],[0,768]],[[0,0,0],[0,0,0],[0,0]],[[0,-6912,11520],[-6912,34560,3424],[11520,3424]],[[0,0,0],[0,0,0],[0,0]],[[-103680,228960,89184],[228960,256608,4512],[89184,4512]],[[0,0,0],[0,0,0],[0,0]],[[600480,2801376,275360],[2801376,759744,2304],[275360,2304]],[[0,0,0],[0,0,0],[0,0]],[[17678304,13220672,444992],[13220672,1185248,480],[444992,480]],[[0,0,0],[0,0,0],[0,0]],[[123318912,34966752,414368],[34966752,1074496,32],[414368,32]],[[0,0,0],[0,0],[0]],[[468611296,58835584,230016],[58835584,585856],[230016]],[[0,0,0],[0,0],[0]],[[1157382240,66872992,75744],[66872992,191296],[75744]],[[0,0,0],[0,0],[0]],[[2008001344,52913856,14016],[52913856,35552],[14016]],[[0,0,0],[0,0],[0]],[[2552629376,29505632,1248],[29505632,3264],[1248]],[[0,0,0],[0,0],[0]],[[2436741088,11571232,32],[11571232,96],[32]],[[0,0],[0]],[[1771087488,3136448],[3136448]],[[0,0],[0]],[[986125568,564992],[564992]],[[0,0],[0]],[[420386048,62528],[62528]],[[0,0],[0]],[[136198816,3584],[3584]],[[0,0],[0]],[[33011040,64],[64]],[[0]],[[5822400]],[[0]],[[712960]],[[0]],[[55712]],[[0]],[[2336]],[[0]],[[32]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
