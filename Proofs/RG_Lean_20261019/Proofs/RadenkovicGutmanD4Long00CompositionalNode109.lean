/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e109 : NestedArithmetic.Expr 3 := .pow e042 2
noncomputable def p109 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,144],[0,288,-96],[144,-96,16]],[[0,0,0],[0,0,0],[0,0]],[[0,7776,384],[7776,-1824,-128],[384,-128]],[[0,0,0],[0,0,0],[0,0]],[[104976,61344,-512],[61344,-18016,256],[-512,256]],[[0,0,0],[0,0,0],[0,0]],[[1376352,182304,-2464],[182304,-49952,480],[-2464,480]],[[0,0,0],[0,0,0],[0,0]],[[8158320,189216,-1568],[189216,-64448,224],[-1568,224]],[[0,0,0],[0,0,0],[0,0]],[[28874016,-253184,2848],[-253184,-39232,32],[2848,32]],[[0,0,0],[0,0],[0]],[[67870224,-1059488,5264],[-1059488,-5536],[5264]],[[0,0,0],[0,0],[0]],[[111423936,-1544032,3616],[-1544032,6240],[3616]],[[0,0,0],[0,0],[0]],[[130560928,-1276128,1264],[-1276128,3680],[1264]],[[0,0,0],[0,0],[0]],[[109117536,-630368,224],[-630368,800],[224]],[[0,0,0],[0,0],[0]],[[63073600,-164544,16],[-164544,64],[16]],[[0,0],[0]],[[22644160,-3040],[-3040]],[[0,0],[0]],[[2705344,12608],[12608]],[[0,0],[0]],[[-1838880,4096],[4096]],[[0,0],[0]],[[-1118448,576],[576]],[[0,0],[0]],[[-257344,32],[32]],[[0]],[[-6240]],[[0]],[[11680]],[[0]],[[3088]],[[0]],[[352]],[[0]],[[16]]]
theorem step109 : p109=NestedArithmetic.power p042 2 := by decide +kernel
#print axioms step109
theorem h109 : NestedArithmetic.compile e109=p109 := StagedExprCompile.compile_pow 2 e109 e042 p042 p109 rfl h042 step109
#print axioms h109
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
