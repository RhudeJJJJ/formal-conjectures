/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode050
import Proofs.RadenkovicGutmanD3Long00StagedUNode052
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .times e050 e052
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,216],[0,216,6]],[[0,0,0],[0,0,0],[0,0]],[[-729,486,1215],[486,4968,774],[1215,774]],[[0,0,0],[0,0,0],[0,0]],[[-3402,33534,7776],[33534,32040,972],[7776,972]],[[0,0,0],[0,0,0],[0,0]],[[194319,286740,20736],[286740,86124,534],[20736,534]],[[0,0,0],[0,0,0],[0,0]],[[2339010,1140660,30258],[1140660,126528,132],[30258,132]],[[0,0,0],[0,0,0],[0,0]],[[12599667,2693124,26622],[2693124,111816,12],[26622,12]],[[0,0,0],[0,0],[0]],[[41245026,4176786,14658],[4176786,61632],[14658]],[[0,0,0],[0,0],[0]],[[91877118,4480536,5064],[4480536,21228],[5064]],[[0,0,0],[0,0],[0]],[[147614568,3416010,1062],[3416010,4416],[1062]],[[0,0,0],[0,0],[0]],[[176961228,1873290,123],[1873290,504],[123]],[[0,0,0],[0,0],[0]],[[161584872,738852,6],[738852,24],[6]],[[0,0],[0]],[[113736540,207000],[207000]],[[0,0],[0]],[[62055240,40026],[40026]],[[0,0],[0]],[[26241987,5052],[5052]],[[0,0],[0]],[[8551122,372],[372]],[[0,0],[0]],[[2120166,12],[12]],[[0]],[[391320]],[[0]],[[51855]],[[0]],[[4638]],[[0]],[[249]],[[0]],[[6]]]
theorem step099 : p099=NestedArithmetic.mul p050 p052 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := by
  change NestedArithmetic.mul (NestedArithmetic.compile e050) (NestedArithmetic.compile e052)=p099
  rw [h050,h052]
  exact step099.symm
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
