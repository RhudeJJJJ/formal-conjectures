/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode089
import Proofs.RadenkovicGutmanD7Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,294],[0,294,-70]],[[0,0,0],[0,0,0],[0,0]],[[0,0,3528],[0,11907,56],[3528,56]],[[0,0,0],[0,0,0],[0,0]],[[9639,96957,20874],[96957,64386,-1610],[20874,-1610]],[[0,0,0],[0,0,0],[0,0]],[[804951,884142,49532],[884142,133203,-2170],[49532,-2170]],[[0,0,0],[0,0,0],[0,0]],[[9041382,3535623,58338],[3535623,121142,-924],[58338,-924]],[[0,0,0],[0,0,0],[0,0]],[[48643791,8152956,32438],[8152956,20972,-126],[32438,-126]],[[0,0,0],[0,0],[0]],[[159726833,11992729,2646],[11992729,-50666],[2646]],[[0,0,0],[0,0],[0]],[[354846926,11735374,-6384],[11735374,-45381],[-6384]],[[0,0,0],[0,0],[0]],[[563222408,7689962,-3402],[7689962,-17038],[-3402]],[[0,0,0],[0,0],[0]],[[658860293,3261076,-714],[3261076,-3101],[-714]],[[0,0,0],[0,0],[0]],[[577842006,778211,-56],[778211,-224],[-56]],[[0,0],[0]],[[382560822,28854],[28854]],[[0,0],[0]],[[190661968,-43001],[-43001]],[[0,0],[0]],[[70477337,-13664],[-13664]],[[0,0],[0]],[[18643429,-1841],[-1841]],[[0,0],[0]],[[3231214,-98],[-98]],[[0]],[[262388]],[[0]],[[-23373]],[[0]],[[-9051]],[[0]],[[-1001]],[[0]],[[-42]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
