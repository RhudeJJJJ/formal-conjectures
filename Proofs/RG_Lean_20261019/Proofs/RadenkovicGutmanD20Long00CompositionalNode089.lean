/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode033
import Proofs.RadenkovicGutmanD20Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1200],[0,1200,-720]],[[0,0,0],[0,0,0],[0,0]],[[0,-10800,10800],[-10800,39600,-7760],[10800,-7760]],[[0,0,0],[0,0,0],[0,0]],[[-103680,118800,17280],[118800,37920,-28160],[17280,-28160]],[[0,0,0],[0,0,0],[0,0]],[[-15120,620640,-102240],[620640,-514960,-28880],[-102240,-28880]],[[0,0,0],[0,0,0],[0,0]],[[3652560,-838480,-397040],[-838480,-1771360,-11120],[-397040,-11120]],[[0,0,0],[0,0,0],[0,0]],[[11737200,-11375520,-609600],[-11375520,-2616000,-1440],[-609600,-1440]],[[0,0,0],[0,0],[0]],[[-14372960,-34358800,-510320],[-34358800,-2141280],[-510320]],[[0,0,0],[0,0],[0]],[[-184278880,-57555200,-250400],[-57555200,-1034000],[-250400]],[[0,0,0],[0,0],[0]],[[-590357280,-62388080,-71760],[-62388080,-292640],[-71760]],[[0,0,0],[0,0],[0]],[[-1126218640,-46313040,-11120],[-46313040,-44880],[-11120]],[[0,0,0],[0,0],[0]],[[-1482112640,-24046560,-720],[-24046560,-2880],[-720]],[[0,0],[0]],[[-1424317440,-8731200],[-8731200]],[[0,0],[0]],[[-1026656640,-2172800],[-2172800]],[[0,0],[0]],[[-561652400,-353120],[-353120]],[[0,0],[0]],[[-233629920,-33760],[-33760]],[[0,0],[0]],[[-73378080,-1440],[-1440]],[[0]],[[-17105760]],[[0]],[[-2867760]],[[0]],[[-326720]],[[0]],[[-22640]],[[0]],[[-720]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
