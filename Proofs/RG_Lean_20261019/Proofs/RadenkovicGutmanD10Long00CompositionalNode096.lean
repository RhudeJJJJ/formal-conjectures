/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode043
import Proofs.RadenkovicGutmanD10Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,300],[0,300,-160]],[[0,0,0],[0,0,0],[0,0]],[[0,2700,2700],[2700,11520,-1580],[2700,-1580]],[[0,0,0],[0,0,0],[0,0]],[[68040,114480,5940],[114480,30000,-6080],[5940,-6080]],[[0,0,0],[0,0,0],[0,0]],[[1594080,740160,-16920],[740160,-46480,-6340],[-16920,-6340]],[[0,0,0],[0,0,0],[0,0]],[[13085280,2051560,-79820],[2051560,-282640,-2460],[-79820,-2460]],[[0,0,0],[0,0,0],[0,0]],[[57846240,2616840,-128400],[2616840,-478080,-320],[-128400,-320]],[[0,0,0],[0,0],[0]],[[160836840,199280,-109860],[199280,-419440],[-109860]],[[0,0,0],[0,0],[0]],[[301820000,-4575000,-54600],[-4575000,-211920],[-54600]],[[0,0,0],[0,0],[0]],[[392992480,-7809260,-15780],[-7809260,-62000],[-15780]],[[0,0,0],[0,0],[0]],[[351142120,-7133420,-2460],[-7133420,-9760],[-2460]],[[0,0,0],[0,0],[0]],[[196453480,-4185100,-160],[-4185100,-640],[-160]],[[0,0],[0]],[[36827800,-1648200],[-1648200]],[[0,0],[0]],[[-45152000,-434700],[-434700]],[[0,0],[0]],[[-52005520,-73800],[-73800]],[[0,0],[0]],[[-29885160,-7300],[-7300]],[[0,0],[0]],[[-11330160,-320],[-320]],[[0]],[[-2989600]],[[0]],[[-547000]],[[0]],[[-66480]],[[0]],[[-4840]],[[0]],[[-160]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
