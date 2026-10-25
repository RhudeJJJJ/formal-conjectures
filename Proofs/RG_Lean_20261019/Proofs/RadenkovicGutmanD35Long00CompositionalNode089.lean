/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode033
import Proofs.RadenkovicGutmanD35Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3675],[0,3675,-2310]],[[0,0,0],[0,0,0],[0,0]],[[0,-33075,33075],[-33075,121275,-25655],[33075,-25655]],[[0,0,0],[0,0,0],[0,0]],[[-309015,363825,44415],[363825,82110,-91280],[44415,-91280]],[[0,0,0],[0,0,0],[0,0]],[[101115,1747620,-358470],[1747620,-1758505,-93065],[-358470,-93065]],[[0,0,0],[0,0,0],[0,0]],[[11636730,-3792565,-1317995],[-3792565,-5833030,-35735],[-1317995,-35735]],[[0,0,0],[0,0,0],[0,0]],[[33803175,-39226110,-1992900],[-39226110,-8515500,-4620],[-1992900,-4620]],[[0,0,0],[0,0],[0]],[[-64431605,-114522625,-1655885],[-114522625,-6929790],[-1655885]],[[0,0,0],[0,0],[0]],[[-639712990,-189218750,-808850],[-189218750,-3334625],[-808850]],[[0,0,0],[0,0],[0]],[[-1980124440,-203552615,-231105],[-203552615,-941570],[-231105]],[[0,0,0],[0,0],[0]],[[-3723200845,-150367245,-35735],[-150367245,-144165],[-35735]],[[0,0,0],[0,0],[0]],[[-4859662220,-77805630,-2310],[-77805630,-9240],[-2310]],[[0,0],[0]],[[-4645066020,-28178850],[-28178850]],[[0,0],[0]],[[-3335356920,-6998600],[-6998600]],[[0,0],[0]],[[-1819403075,-1135610],[-1135610]],[[0,0],[0]],[[-755105085,-108430],[-108430]],[[0,0],[0]],[[-236730690,-4620],[-4620]],[[0]],[[-55103580]],[[0]],[[-9226455]],[[0]],[[-1050035]],[[0]],[[-72695]],[[0]],[[-2310]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
