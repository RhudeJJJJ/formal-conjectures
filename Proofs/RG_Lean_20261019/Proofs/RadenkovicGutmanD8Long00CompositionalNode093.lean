/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode033
import Proofs.RadenkovicGutmanD8Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,1536],[0,1536,16]],[[0,0,0],[0,0,0],[0,0]],[[-5184,-3456,8640],[-3456,33408,5024],[8640,5024]],[[0,0,0],[0,0,0],[0,0]],[[-142992,131328,53136],[131328,202560,5632],[53136,5632]],[[0,0,0],[0,0,0],[0,0]],[[-625536,1304352,135936],[1304352,509824,2624],[135936,2624]],[[0,0,0],[0,0,0],[0,0]],[[1416624,5280640,189248],[5280640,698368,512],[189248,512]],[[0,0,0],[0,0,0],[0,0]],[[21225536,12326208,157312],[12326208,572416,32],[157312,32]],[[0,0,0],[0,0],[0]],[[89239536,18723328,80608],[18723328,290432],[80608]],[[0,0,0],[0,0],[0]],[[222805760,19598048,25344],[19598048,91008],[25344]],[[0,0,0],[0,0],[0]],[[382181472,14545024,4672],[14545024,16896],[4672]],[[0,0,0],[0,0],[0]],[[478432960,7742720,448],[7742720,1664],[448]],[[0,0,0],[0,0],[0]],[[450834240,2951808,16],[2951808,64],[16]],[[0,0],[0]],[[325099072,794080],[794080]],[[0,0],[0]],[[180753408,145920],[145920]],[[0,0],[0]],[[77540544,17216],[17216]],[[0,0],[0]],[[25518576,1152],[1152]],[[0,0],[0]],[[6359424,32],[32]],[[0]],[[1173088]],[[0]],[[154240]],[[0]],[[13552]],[[0]],[[704]],[[0]],[[16]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
