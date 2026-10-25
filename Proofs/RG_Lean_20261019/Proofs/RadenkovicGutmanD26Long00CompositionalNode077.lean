/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,6084],[0,12168],[6084]],[[0,0,0],[0,0],[0]],[[0,200772,52728],[200772,105456],[52728]],[[0,0,0],[0,0],[0]],[[1642680,2244996,179140],[2244996,358280],[179140]],[[0,0,0],[0,0],[0]],[[22449960,10726092,309608],[10726092,619216],[309608]],[[0,0,0],[0,0],[0]],[[136853496,29034200,300144],[29034200,600288],[300144]],[[0,0,0],[0,0],[0]],[[495383616,49836748,169000],[49836748,338000],[169000]],[[0,0,0],[0,0],[0]],[[1195570896,57417412,54756],[57417412,109512],[54756]],[[0,0,0],[0,0],[0]],[[2045654416,45721936,9464],[45721936,18928],[9464]],[[0,0,0],[0,0],[0]],[[2573130456,25457484,676],[25457484,1352],[676]],[[0,0],[0]],[[2432219608,9875684],[9875684]],[[0,0],[0]],[[1749304128,2613416],[2613416]],[[0,0],[0]],[[962203528,449540],[449540]],[[0,0],[0]],[[404124968,45292],[45292]],[[0,0],[0]],[[128458928,2028],[2028]],[[0]],[[30346992]],[[0]],[[5159232]],[[0]],[[596232]],[[0]],[[41912]],[[0]],[[1352]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
