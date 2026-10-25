/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode217
import Proofs.RadenkovicGutmanD38Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-2888],[0],[0]],[[0,0],[0,0],[0]],[[-89528,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-1273608,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-11020608,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-64824048,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-274400432,-4332,0],[-4332,0],[0]],[[0,0,0],[0,0],[0]],[[-863249192,-96748,0],[-96748,0],[0]],[[0,0,0],[0,0],[0]],[[-2055357832,-960260,0],[-960260,0],[0]],[[0,0,0],[0,0],[0]],[[-3736679232,-5582504,0],[-5582504,0],[0]],[[0,0,0],[0,0],[0]],[[-5195451352,-21095396,0],[-21095396,0],[0]],[[0,0,0],[0,0],[0]],[[-5496450264,-54379596,-1444],[-54379596,-2888],[-1444]],[[0,0,0],[0,0],[0]],[[-4369711504,-97666384,-20216],[-97666384,-40432],[-20216]],[[0,0,0],[0,0],[0]],[[-2553852624,-122649028,-116964],[-122649028,-233928],[-116964]],[[0,0,0],[0,0],[0]],[[-1058186304,-106456012,-361000],[-106456012,-722000],[-361000]],[[0,0,0],[0,0],[0]],[[-292332024,-62019800,-641136],[-62019800,-1282272],[-641136]],[[0,0,0],[0,0],[0]],[[-47955240,-22911948,-661352],[-22911948,-1322704],[-661352]],[[0,0,0],[0,0],[0]],[[-3508920,-4795524,-382660],[-4795524,-765320],[-382660]],[[0,0,0],[0,0],[0]],[[0,-428868,-112632],[-428868,-225264],[-112632]],[[0,0,0],[0,0],[0]],[[0,0,-12996],[0,-25992],[-12996]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
