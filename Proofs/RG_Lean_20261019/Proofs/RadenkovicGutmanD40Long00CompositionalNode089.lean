/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode033
import Proofs.RadenkovicGutmanD40Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4800],[0,4800,-3040]],[[0,0,0],[0,0,0],[0,0]],[[0,-43200,43200],[-43200,158400,-33920],[43200,-33920]],[[0,0,0],[0,0,0],[0,0]],[[-401760,475200,56160],[475200,99840,-120320],[56160,-120320]],[[0,0,0],[0,0,0],[0,0]],[[164160,2249280,-478080],[2249280,-2336320,-122560],[-478080,-122560]],[[0,0,0],[0,0,0],[0,0]],[[15297120,-5220160,-1743680],[-5220160,-7707520,-47040],[-1743680,-47040]],[[0,0,0],[0,0,0],[0,0]],[[43684800,-52189440,-2630400],[-52189440,-11232000,-6080],[-2630400,-6080]],[[0,0,0],[0,0],[0]],[[-88599520,-151604800,-2183040],[-151604800,-9132160],[-2183040]],[[0,0,0],[0,0],[0]],[[-851948160,-249963200,-1065600],[-249963200,-4392000],[-1065600]],[[0,0,0],[0,0],[0]],[[-2623760960,-268583360,-304320],[-268583360,-1239680],[-304320]],[[0,0,0],[0,0],[0]],[[-4922636480,-198255680,-47040],[-198255680,-189760],[-47040]],[[0,0,0],[0,0],[0]],[[-6417124480,-102529920,-3040],[-102529920,-12160],[-3040]],[[0,0],[0]],[[-6128650880,-37118400],[-37118400]],[[0,0],[0]],[[-4398010880,-9216000],[-9216000]],[[0,0],[0]],[[-2397988800,-1495040],[-1495040]],[[0,0],[0]],[[-994883040,-142720],[-142720]],[[0,0],[0]],[[-311813760,-6080],[-6080]],[[0]],[[-72563520]],[[0]],[[-12147520]],[[0]],[[-1382240]],[[0]],[[-95680]],[[0]],[[-3040]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
