/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,676]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-12168,12168],[0,12168]],[[0,0,0],[0,0,0],[0,0]],[[54756,-109512,54756],[-109512,113568,32448],[54756,32448]],[[0,0,0],[0,0,0],[0,0]],[[-36504,-255528,292032],[-255528,809848,29744],[292032,29744]],[[0,0,0],[0,0,0],[0,0]],[[-2025972,1861704,657072],[1861704,2009072,10816],[657072,10816]],[[0,0,0],[0,0,0],[0,0]],[[-5577000,11665056,811200],[11665056,2644512,1352],[811200,1352]],[[0,0,0],[0,0],[0]],[[11738740,30864808,598936],[30864808,2057744],[598936]],[[0,0,0],[0,0],[0]],[[111380464,49368280,270400],[49368280,972088],[270400]],[[0,0,0],[0,0],[0]],[[347987224,52790192,73008],[52790192,273104],[73008]],[[0,0,0],[0,0],[0]],[[669114264,39283712,10816],[39283712,41912],[10816]],[[0,0,0],[0,0],[0]],[[900556384,20622056,676],[20622056,2704],[676]],[[0,0],[0]],[[893017632,7605000],[7605000]],[[0,0],[0]],[[668207072,1926600],[1926600]],[[0,0],[0]],[[381027400,319072],[319072]],[[0,0],[0]],[[165645012,31096],[31096]],[[0,0],[0]],[[54461264,1352],[1352]],[[0]],[[13302328]],[[0]],[[2337608]],[[0]],[[279188]],[[0]],[[20280]],[[0]],[[676]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
