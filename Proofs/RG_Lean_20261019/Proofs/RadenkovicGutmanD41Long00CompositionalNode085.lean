/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode073
import Proofs.RadenkovicGutmanD41Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2952,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26568,-389664,0],[-389664,-86838,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6697350,-5572638,0],[-5572638,-617788,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-104936958,-33973092,0],[-33973092,-1953814,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-749894592,-116781530,0],[-116781530,-3262780,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3190867558,-253010836,0],[-253010836,-3103864,0],[0,0]],[[0,0,0],[0,0],[0]],[[-9038560618,-366504330,0],[-366504330,-1728068],[0]],[[0,0,0],[0,0],[0]],[[-18112232324,-367261272,0],[-367261272,-555878],[0]],[[0,0,0],[0,0],[0]],[[-26648698496,-259290724,0],[-259290724,-95612],[0]],[[0,0,0],[0,0],[0]],[[-29479818442,-129734168,0],[-129734168,-6806],[0]],[[0,0,0],[0,0],[0]],[[-24887566948,-45687858,0],[-45687858,0],[0]],[[0,0],[0]],[[-16166451700,-11064260],[-11064260]],[[0,0],[0]],[[-8099943928,-1752914],[-1752914]],[[0,0],[0]],[[-3119851130,-163508],[-163508]],[[0,0],[0]],[[-914535586,-6806],[-6806]],[[0,0],[0]],[[-200172660,0],[0]],[[0]],[[-31656920]],[[0]],[[-3415054]],[[0]],[[-224762]],[[0]],[[-6806]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
