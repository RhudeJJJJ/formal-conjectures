/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode035
import Proofs.RadenkovicGutmanD9Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-729],[0,-1458,378],[-729,378]],[[0,0,0],[0,0,0],[0,0]],[[0,-20655,-2916],[-20655,972,1638],[-2916,1638]],[[0,0,0],[0,0,0],[0,0]],[[-135594,-132921,2349],[-132921,52326,2016],[2349,2016]],[[0,0,0],[0,0,0],[0,0]],[[-1179522,-151227,28674],[-151227,188892,882],[28674,882]],[[0,0,0],[0,0,0],[0,0]],[[-2898990,1008414,59418],[1008414,309600,126],[59418,126]],[[0,0,0],[0,0],[0]],[[6200712,4514913,59886],[4514913,280044],[59886]],[[0,0,0],[0,0],[0]],[[59497632,9062631,33633],[9062631,147654],[33633]],[[0,0,0],[0,0],[0]],[[188191548,11094264,10710],[11094264,45108],[10710]],[[0,0,0],[0,0],[0]],[[362814570,9030123,1809],[9030123,7398],[1809]],[[0,0,0],[0,0],[0]],[[484374366,5045733,126],[5045733,504],[126]],[[0,0],[0]],[[471856716,1945908],[1945908]],[[0,0],[0]],[[344104146,509355],[509355]],[[0,0],[0]],[[190069542,86427],[86427]],[[0,0],[0]],[[79686324,8577],[8577]],[[0,0],[0]],[[25188768,378],[378]],[[0]],[[5903064]],[[0]],[[994014]],[[0]],[[113670]],[[0]],[[7902]],[[0]],[[252]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
