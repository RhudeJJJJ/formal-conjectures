/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode264
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e265 : NestedArithmetic.Expr 3 := .times e264 e003
noncomputable def p265 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[32,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[992,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[14080,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[121184,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[705984,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2942048,48,0],[48,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[9033024,1072,0],[1072,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[20719712,10592,0],[10592,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[35562176,60880,0],[60880,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[45131296,225008,0],[225008,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[40948096,557248,16],[557248,64,0],[16,0]],[[0,0,0],[0,0,0],[0,0]],[[24320800,931488,224],[931488,928,0],[224,0]],[[0,0,0],[0,0,0],[0,0]],[[6605248,1022304,1280],[1022304,5568,0],[1280,0]],[[0,0,0],[0,0,0],[0,0]],[[-2551008,665456,3808],[665456,17824,0],[3808,0]],[[0,0,0],[0,0,0],[0,0]],[[-3400128,152048,6176],[152048,32704,0],[6176,0]],[[0,0,0],[0,0,0],[0,0]],[[-1524960,-117376,5008],[-117376,34240,16],[5008,16]],[[0,0,0],[0,0,0],[0,0]],[[-339552,-109872,1024],[-109872,18752,112],[1024,112]],[[0,0,0],[0,0,0],[0,0]],[[-31104,-35856,-1216],[-35856,3616,256],[-1216,256]],[[0,0,0],[0,0,0],[0,0]],[[0,-4320,-816],[-4320,-768,208],[-816,208]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-144],[0,-288,48],[-144,48]]]
theorem step265 : p265=NestedArithmetic.mul p264 p003 := by decide +kernel
#print axioms step265
theorem h265 : NestedArithmetic.compile e265=p265 := StagedExprCompile.compile_times e265 e264 e003 p264 p003 p265 rfl h264 h003 step265
#print axioms h265
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
