/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode035
import Proofs.RadenkovicGutmanD30Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-8100],[0,-16200,5040],[-8100,5040]],[[0,0,0],[0,0,0],[0,0]],[[0,-221940,-24840],[-221940,41040,21840],[-24840,21840]],[[0,0,0],[0,0,0],[0,0]],[[-1370520,-1174500,79020],[-1174500,793080,26880],[79020,26880]],[[0,0,0],[0,0,0],[0,0]],[[-9749160,839700,464760],[839700,2683440,11760],[464760,11760]],[[0,0,0],[0,0,0],[0,0]],[[-2212920,21176520,872160],[21176520,4287840,1680],[872160,1680]],[[0,0,0],[0,0],[0]],[[214583040,73468980,843480],[73468980,3823920],[843480]],[[0,0,0],[0,0],[0]],[[1111649040,136123740,463020],[136123740,1997880],[463020]],[[0,0,0],[0,0],[0]],[[3053921520,160098000,145320],[160098000,606480],[145320]],[[0,0,0],[0,0],[0]],[[5522680680,127180260,24300],[127180260,99000],[24300]],[[0,0,0],[0,0],[0]],[[7105957320,69906060,1680],[69906060,6720],[1680]],[[0,0],[0]],[[6757213920,26641320],[26641320]],[[0,0],[0]],[[4844263320,6911100],[6911100]],[[0,0],[0]],[[2641867800,1164420],[1164420]],[[0,0],[0]],[[1096689360,114900],[114900]],[[0,0],[0]],[[343930800,5040],[5040]],[[0]],[[80081280]],[[0]],[[13412280]],[[0]],[[1526760]],[[0]],[[105720]],[[0]],[[3360]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
