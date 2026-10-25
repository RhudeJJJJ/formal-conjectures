/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode033
import Proofs.RadenkovicGutmanD8Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,192],[0,192,-96]],[[0,0,0],[0,0,0],[0,0]],[[0,-1728,1728],[-1728,6336,-896],[1728,-896]],[[0,0,0],[0,0,0],[0,0]],[[-18144,19008,4320],[19008,12288,-3584],[4320,-3584]],[[0,0,0],[0,0,0],[0,0]],[[-29376,127296,-8064],[127296,-49216,-3776],[-8064,-3776]],[[0,0,0],[0,0,0],[0,0]],[[501984,89792,-44864],[89792,-208768,-1472],[-44864,-1472]],[[0,0,0],[0,0,0],[0,0]],[[2269632,-1017600,-74496],[-1017600,-326400,-192],[-74496,-192]],[[0,0,0],[0,0],[0]],[[1433248,-3797056,-64640],[-3797056,-274560],[-64640]],[[0,0,0],[0,0],[0]],[[-15704704,-6839744,-32384],[-6839744,-134720],[-32384]],[[0,0,0],[0,0],[0]],[[-62977344,-7698368,-9408],[-7698368,-38528],[-9408]],[[0,0,0],[0,0],[0]],[[-130063552,-5849664,-1472],[-5849664,-5952],[-1472]],[[0,0,0],[0,0],[0]],[[-178497152,-3086208,-96],[-3086208,-384],[-96]],[[0,0],[0]],[[-176125056,-1133760],[-1133760]],[[0,0],[0]],[[-129298944,-284672],[-284672]],[[0,0],[0]],[[-71698880,-46592],[-46592]],[[0,0],[0]],[[-30137184,-4480],[-4480]],[[0,0],[0]],[[-9544320,-192],[-192]],[[0]],[[-2240064]],[[0]],[[-377664]],[[0]],[[-43232]],[[0]],[[-3008]],[[0]],[[-96]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
