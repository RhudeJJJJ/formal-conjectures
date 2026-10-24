/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode034
import Proofs.RadenkovicGutmanD4Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e034 e060
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-144],[0,-288,48],[-144,48]],[[0,0,0],[0,0,0],[0,0]],[[0,-4320,-816],[-4320,-768,208],[-816,208]],[[0,0,0],[0,0,0],[0,0]],[[-31104,-35856,-1216],[-35856,3616,256],[-1216,256]],[[0,0,0],[0,0,0],[0,0]],[[-339552,-109872,1024],[-109872,18752,112],[1024,112]],[[0,0,0],[0,0,0],[0,0]],[[-1524960,-117376,5008],[-117376,34240,16],[5008,16]],[[0,0,0],[0,0],[0]],[[-3400128,152048,6176],[152048,32704],[6176]],[[0,0,0],[0,0],[0]],[[-2551008,665456,3808],[665456,17824],[3808]],[[0,0,0],[0,0],[0]],[[6605248,1022304,1280],[1022304,5568],[1280]],[[0,0,0],[0,0],[0]],[[24320800,931488,224],[931488,928],[224]],[[0,0,0],[0,0],[0]],[[40948096,557248,16],[557248,64],[16]],[[0,0],[0]],[[45131296,225008],[225008]],[[0,0],[0]],[[35562176,60880],[60880]],[[0,0],[0]],[[20719712,10592],[10592]],[[0,0],[0]],[[9033024,1072],[1072]],[[0,0],[0]],[[2942048,48],[48]],[[0]],[[705984]],[[0]],[[121184]],[[0]],[[14080]],[[0]],[[992]],[[0]],[[32]]]
theorem step093 : p093=NestedArithmetic.mul p034 p060 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e034 e060 p034 p060 p093 rfl h034 h060 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
