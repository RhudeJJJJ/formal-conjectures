/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode043
import Proofs.RadenkovicGutmanD6Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-324],[0,-648,144],[-324,144]],[[0,0,0],[0,0,0],[0,0]],[[0,-13284,-1512],[-13284,-864,624],[-1512,624]],[[0,0,0],[0,0,0],[0,0]],[[-126360,-122148,-468],[-122148,13464,768],[-468,768]],[[0,0,0],[0,0,0],[0,0]],[[-1616760,-464508,8568],[-464508,54528,336],[8568,336]],[[0,0,0],[0,0,0],[0,0]],[[-9252792,-933288,20352],[-933288,91392,48],[20352,48]],[[0,0,0],[0,0],[0]],[[-31388400,-987804,21528],[-987804,82800],[21528]],[[0,0,0],[0,0],[0]],[[-70370544,-286788,12396],[-286788,43416],[12396]],[[0,0,0],[0,0],[0]],[[-109803120,644112,4008],[644112,13152],[4008]],[[0,0,0],[0,0],[0]],[[-121837464,1018740,684],[1018740,2136],[684]],[[0,0,0],[0,0],[0]],[[-95677032,762012,48],[762012,144],[48]],[[0,0],[0]],[[-50629824,350232],[350232]],[[0,0],[0]],[[-14622120,103500],[103500]],[[0,0],[0]],[[1360152,19236],[19236]],[[0,0],[0]],[[3742848,2052],[2052]],[[0,0],[0]],[[2014704,96],[96]],[[0]],[[637920]],[[0]],[[131640]],[[0]],[[17496]],[[0]],[[1368]],[[0]],[[48]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
