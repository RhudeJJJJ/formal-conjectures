/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,576],[0,1152,-576],[576,-576,144]],[[0,0,0],[0,0,0],[0,0]],[[0,29376,-192],[29376,-15072,96],[-192,96]],[[0,0,0],[0,0,0],[0,0]],[[374544,168480,-7664],[168480,-102016,3840],[-7664,3840]],[[0,0,0],[0,0,0],[0,0]],[[4421088,181728,-8704],[181728,-220640,4992],[-8704,4992]],[[0,0,0],[0,0,0],[0,0]],[[23411376,-1016992,23040],[-1016992,-184512,2112],[23040,2112]],[[0,0,0],[0,0,0],[0,0]],[[72933024,-4173440,66688],[-4173440,21632,288],[66688,288]],[[0,0,0],[0,0],[0]],[[146814160,-7310240,71520],[-7310240,155712],[71520]],[[0,0,0],[0,0],[0]],[[195709760,-7140128,40448],[-7140128,121120],[40448]],[[0,0,0],[0,0],[0]],[[165301984,-3686016,12736],[-3686016,44096],[12736]],[[0,0,0],[0,0],[0]],[[67470240,-295360,2112],[-295360,7968],[2112]],[[0,0,0],[0,0],[0]],[[-22649216,927392,144],[927392,576],[144]],[[0,0],[0]],[[-51406720,680480],[680480]],[[0,0],[0]],[[-32968448,245536],[245536]],[[0,0],[0]],[[-8657184,51072],[51072]],[[0,0],[0]],[[1945168,5856],[5856]],[[0,0],[0]],[[2654144,288],[288]],[[0]],[[1137760]],[[0]],[[282336]],[[0]],[[42960]],[[0]],[[3744]],[[0]],[[144]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
