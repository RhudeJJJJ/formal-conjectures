/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode033
import Proofs.RadenkovicGutmanD9Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,243],[0,243,-126]],[[0,0,0],[0,0,0],[0,0]],[[0,-2187,2187],[-2187,8019,-1215],[2187,-1215]],[[0,0,0],[0,0,0],[0,0]],[[-22599,24057,5103],[24057,14094,-4752],[5103,-4752]],[[0,0,0],[0,0,0],[0,0]],[[-30861,154548,-12150],[154548,-70065,-4977],[-12150,-4977]],[[0,0,0],[0,0,0],[0,0]],[[654642,61155,-61155],[61155,-281718,-1935],[-61155,-1935]],[[0,0,0],[0,0,0],[0,0]],[[2780703,-1475982,-99684],[-1475982,-434700,-252],[-99684,-252]],[[0,0,0],[0,0],[0]],[[939051,-5204169,-85797],[-5204169,-363438],[-85797]],[[0,0,0],[0,0],[0]],[[-23105934,-9211806,-42786],[-9211806,-177705],[-42786]],[[0,0,0],[0,0],[0]],[[-87083784,-10278495,-12393],[-10278495,-50706],[-12393]],[[0,0,0],[0,0],[0]],[[-176361237,-7769205,-1935],[-7769205,-7821],[-1935]],[[0,0,0],[0,0],[0]],[[-239654412,-4084398,-126],[-4084398,-504],[-126]],[[0,0],[0]],[[-235040868,-1496610],[-1496610]],[[0,0],[0]],[[-171839160,-375048],[-375048]],[[0,0],[0]],[[-95001435,-61290],[-61290]],[[0,0],[0]],[[-39840093,-5886],[-5886]],[[0,0],[0]],[[-12594258,-252],[-252]],[[0]],[[-2951532]],[[0]],[[-497007]],[[0]],[[-56835]],[[0]],[[-3951]],[[0]],[[-126]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
