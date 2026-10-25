/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode043
import Proofs.RadenkovicGutmanD24Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1728],[0,1728,-1056]],[[0,0,0],[0,0,0],[0,0]],[[0,15552,15552],[15552,63936,-11520],[15552,-11520]],[[0,0,0],[0,0,0],[0,0]],[[381024,637632,23328],[637632,108288,-41472],[23328,-41472]],[[0,0,0],[0,0,0],[0,0]],[[8797248,3820608,-155520],[3820608,-571200,-42432],[-155520,-42432]],[[0,0,0],[0,0,0],[0,0]],[[70287264,9051840,-590400],[9051840,-2273664,-16320],[-590400,-16320]],[[0,0,0],[0,0,0],[0,0]],[[299945664,6157440,-900864],[6157440,-3518208,-2112],[-900864,-2112]],[[0,0,0],[0,0],[0]],[[796033248,-16520640,-751872],[-16520640,-2959488],[-751872]],[[0,0,0],[0,0],[0]],[[1397556096,-49704000,-368256],[-49704000,-1457472],[-368256]],[[0,0,0],[0,0],[0]],[[1631077440,-66457920,-105408],[-66457920,-418944],[-105408]],[[0,0,0],[0,0],[0]],[[1156964928,-55124160,-16320],[-55124160,-65088],[-16320]],[[0,0,0],[0,0],[0]],[[236291712,-30663552,-1056],[-30663552,-4224],[-1056]],[[0,0],[0]],[[-498353280,-11666880],[-11666880]],[[0,0],[0]],[[-696198144,-3002496],[-3002496]],[[0,0],[0]],[[-507062976,-500352],[-500352]],[[0,0],[0]],[[-248383776,-48768],[-48768]],[[0,0],[0]],[[-86668416,-2112],[-2112]],[[0]],[[-21723840]],[[0]],[[-3837504]],[[0]],[[-454560]],[[0]],[[-32448]],[[0]],[[-1056]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
