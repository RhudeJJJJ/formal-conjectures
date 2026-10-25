/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode051
import Proofs.RadenkovicGutmanD10Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,100]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,2400],[0,2400,20]],[[0,0,0],[0,0,0],[0,0]],[[-8100,5400,13500],[5400,54360,7760],[13500,7760]],[[0,0,0],[0,0,0],[0,0]],[[-41580,365040,82620],[365040,333600,8560],[82620,8560]],[[0,0,0],[0,0,0],[0,0]],[[2025540,3032280,210240],[3032280,851560,3880],[210240,3880]],[[0,0,0],[0,0,0],[0,0]],[[24223740,11713880,290840],[11713880,1181680,720],[290840,720]],[[0,0,0],[0,0,0],[0,0]],[[128451620,26827920,239800],[26827920,976960,40],[239800,40]],[[0,0,0],[0,0],[0]],[[413004820,40273840,121520],[40273840,496080],[121520]],[[0,0,0],[0,0],[0]],[[902479400,41675400,37600],[41675400,153640],[37600]],[[0,0,0],[0,0],[0]],[[1420523240,30498520,6760],[30498520,27600],[6760]],[[0,0,0],[0,0],[0]],[[1665675560,15940840,620],[15940840,2520],[620]],[[0,0,0],[0,0],[0]],[[1484526240,5932600,20],[5932600,80],[20]],[[0,0],[0]],[[1017044400,1545400],[1545400]],[[0,0],[0]],[[538071200,271600],[271600]],[[0,0],[0]],[[219525140,30000],[30000]],[[0,0],[0]],[[68538420,1800],[1800]],[[0,0],[0]],[[16124520,40],[40]],[[0]],[[2784200]],[[0]],[[337700]],[[0]],[[26660]],[[0]],[[1180]],[[0]],[[20]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
