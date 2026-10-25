/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode071
import Proofs.RadenkovicGutmanD39Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-82134,0],[-82134,-16497,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1380483,-1544751,0],[-1544751,-198432,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-28227771,-12393810,0],[-12393810,-966381,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-256095918,-56234295,0],[-56234295,-2472444,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1371232629,-161282862,0],[-161282862,-3636048,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4863382251,-309940917,0],[-309940917,-3194178,0],[0,0]],[[0,0,0],[0,0],[0]],[[-12159999228,-413178402,0],[-413178402,-1688973],[0]],[[0,0,0],[0,0],[0]],[[-22272630744,-390126204,0],[-390126204,-524784],[0]],[[0,0,0],[0,0],[0]],[[-30646354011,-263657550,0],[-263657550,-88101],[0]],[[0,0,0],[0,0],[0]],[[-32208761364,-127658271,0],[-127658271,-6162],[0]],[[0,0,0],[0,0],[0]],[[-26125389654,-43839354,0],[-43839354,0],[0]],[[0,0],[0]],[[-16440328788,-10409997],[-10409997]],[[0,0],[0]],[[-8029368243,-1623726],[-1623726]],[[0,0],[0]],[[-3028927083,-149565],[-149565]],[[0,0],[0]],[[-872772420,-6162],[-6162]],[[0,0],[0]],[[-188320860,0],[0]],[[0]],[[-29427021]],[[0]],[[-3142347]],[[0]],[[-205023]],[[0]],[[-6162]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
