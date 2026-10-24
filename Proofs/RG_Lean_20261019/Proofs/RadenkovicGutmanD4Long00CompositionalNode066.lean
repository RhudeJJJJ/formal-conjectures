/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode042
import Proofs.RadenkovicGutmanD4Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e042 e060
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,144],[0,288,-96],[144,-96,16]],[[0,0,0],[0,0,0],[0,0]],[[0,5616,384],[5616,-1104,-128],[384,-128]],[[0,0,0],[0,0,0],[0,0]],[[46656,39744,-512],[39744,-11776,256],[-512,256]],[[0,0,0],[0,0,0],[0,0]],[[488592,99504,-2464],[99504,-28752,480],[-2464,480]],[[0,0,0],[0,0,0],[0,0]],[[2114640,55216,-1568],[55216,-27808,224],[-1568,224]],[[0,0,0],[0,0,0],[0,0]],[[4489776,-238064,2848],[-238064,-3712,32],[2848,32]],[[0,0,0],[0,0],[0]],[[2742144,-606048,5264],[-606048,14464],[5264]],[[0,0,0],[0,0],[0]],[[-10351264,-655072,3616],[-655072,12720],[3616]],[[0,0,0],[0,0],[0]],[[-33682432,-334928,1264],[-334928,4800],[1264]],[[0,0,0],[0,0],[0]],[[-52862864,2032,224],[2032,880],[224]],[[0,0,0],[0,0],[0]],[[-53652960,116816,16],[116816,64],[16]],[[0,0],[0]],[[-37604160,79760],[79760]],[[0,0],[0]],[[-18233696,28128],[28128]],[[0,0],[0]],[[-5734640,5776],[5776]],[[0,0],[0]],[[-846528,656],[656]],[[0,0],[0]],[[156576,32],[32]],[[0]],[[122880]],[[0]],[[33360]],[[0]],[[5088]],[[0]],[[432]],[[0]],[[16]]]
theorem step066 : p066=NestedArithmetic.mul p042 p060 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e042 e060 p042 p060 p066 rfl h042 h060 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
