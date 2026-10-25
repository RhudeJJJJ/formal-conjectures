/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode043
import Proofs.RadenkovicGutmanD20Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1200],[0,1200,-720]],[[0,0,0],[0,0,0],[0,0]],[[0,10800,10800],[10800,44640,-7760],[10800,-7760]],[[0,0,0],[0,0,0],[0,0]],[[265680,444960,17280],[444960,81600,-28160],[17280,-28160]],[[0,0,0],[0,0,0],[0,0]],[[6147360,2697120,-102240],[2697120,-366560,-28880],[-102240,-28880]],[[0,0,0],[0,0,0],[0,0]],[[49314960,6560320,-397040],[6560320,-1514880,-11120],[-397040,-11120]],[[0,0,0],[0,0,0],[0,0]],[[211594080,5160480,-609600],[5160480,-2367360,-1440],[-609600,-1440]],[[0,0,0],[0,0],[0]],[[565736080,-9719840,-510320],[-9719840,-2001280],[-510320]],[[0,0,0],[0,0],[0]],[[1004347200,-32200000,-250400],[-32200000,-988640],[-250400]],[[0,0,0],[0,0],[0]],[[1195446560,-44020720,-71760],[-44020720,-284800],[-71760]],[[0,0,0],[0,0],[0]],[[889322240,-36888240,-11120],[-36888240,-44320],[-11120]],[[0,0,0],[0,0],[0]],[[252908960,-20643600,-720],[-20643600,-2880],[-720]],[[0,0],[0]],[[-275594400,-7886400],[-7886400]],[[0,0],[0]],[[-440204800,-2035600],[-2035600]],[[0,0],[0]],[[-331540640,-340000],[-340000]],[[0,0],[0]],[[-164924720,-33200],[-33200]],[[0,0],[0]],[[-58062720,-1440],[-1440]],[[0]],[[-14639200]],[[0]],[[-2596800]],[[0]],[[-308560]],[[0]],[[-22080]],[[0]],[[-720]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
