/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,289]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-5202,5202],[0,5202]],[[0,0,0],[0,0,0],[0,0]],[[23409,-46818,23409],[-46818,48552,13872],[23409,13872]],[[0,0,0],[0,0,0],[0,0]],[[-15606,-109242,124848],[-109242,346222,12716],[124848,12716]],[[0,0,0],[0,0,0],[0,0]],[[-866133,795906,280908],[795906,858908,4624],[280908,4624]],[[0,0,0],[0,0,0],[0,0]],[[-2384250,4986984,346800],[4986984,1130568,578],[346800,578]],[[0,0,0],[0,0],[0]],[[5018485,13195162,256054],[13195162,879716],[256054]],[[0,0,0],[0,0],[0]],[[47616796,21105670,115600],[21105670,415582],[115600]],[[0,0,0],[0,0],[0]],[[148769686,22568588,31212],[22568588,116756],[31212]],[[0,0,0],[0,0],[0]],[[286056246,16794368,4624],[16794368,17918],[4624]],[[0,0,0],[0,0],[0]],[[385001176,8816234,289],[8816234,1156],[289]],[[0,0],[0]],[[381778248,3251250],[3251250]],[[0,0],[0]],[[285668408,823650],[823650]],[[0,0],[0]],[[162894850,136408],[136408]],[[0,0],[0]],[[70815693,13294],[13294]],[[0,0],[0]],[[23282996,578],[578]],[[0]],[[5686942]],[[0]],[[999362]],[[0]],[[119357]],[[0]],[[8670]],[[0]],[[289]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
