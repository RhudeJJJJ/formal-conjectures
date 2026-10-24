/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode033
import Proofs.RadenkovicGutmanD5Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,450],[0,450]],[[0,0,0],[0,0,0],[0,0]],[[-2025,0,2025],[0,8100,1200],[2025,1200]],[[0,0,0],[0,0,0],[0,0]],[[-35100,36450,10800],[36450,43200,1100],[10800,1100]],[[0,0,0],[0,0,0],[0,0]],[[-107325,291600,24300],[291600,97200,400],[24300,400]],[[0,0,0],[0,0,0],[0,0]],[[510000,1044900,30000],[1044900,120000,50],[30000,50]],[[0,0,0],[0,0],[0]],[[4860575,2214000,22150],[2214000,88600],[22150]],[[0,0,0],[0,0],[0]],[[17942600,3084750,10000],[3084750,40000],[10000]],[[0,0,0],[0,0],[0]],[[40989350,2973600,2700],[2973600,10800],[2700]],[[0,0,0],[0,0],[0]],[[65275300,2031800,400],[2031800,1600],[400]],[[0,0,0],[0,0],[0]],[[76355300,991200,25],[991200,100],[25]],[[0,0],[0]],[[67403300,342750],[342750]],[[0,0],[0]],[[45528800,82000],[82000]],[[0,0],[0]],[[23653000,12900],[12900]],[[0,0],[0]],[[9431775,1200],[1200]],[[0,0],[0]],[[2859600,50],[50]],[[0]],[[646950]],[[0]],[[105700]],[[0]],[[11775]],[[0]],[[800]],[[0]],[[25]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
