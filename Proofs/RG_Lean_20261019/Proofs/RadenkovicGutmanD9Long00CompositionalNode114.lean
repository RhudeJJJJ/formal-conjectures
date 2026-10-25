/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,729],[0,1458],[729]],[[0,0,0],[0,0],[0]],[[0,26244,6318],[26244,12636],[6318]],[[0,0,0],[0,0],[0]],[[236196,297432,21465],[297432,42930],[21465]],[[0,0,0],[0,0],[0]],[[3306744,1443420,37098],[1443420,74196],[37098]],[[0,0,0],[0,0],[0]],[[20706516,3975480,35964],[3975480,71928],[35964]],[[0,0,0],[0,0],[0]],[[77174856,6950124,20250],[6950124,40500],[20250]],[[0,0,0],[0,0],[0]],[[192123576,8158320,6561],[8158320,13122],[6561]],[[0,0,0],[0,0],[0]],[[339533208,6618024,1134],[6618024,2268],[1134]],[[0,0,0],[0,0],[0]],[[441511884,3751920,81],[3751920,162],[81]],[[0,0],[0]],[[431659368,1481004],[1481004]],[[0,0],[0]],[[321188328,398520],[398520]],[[0,0],[0]],[[182775528,69660],[69660]],[[0,0],[0]],[[79406892,7128],[7128]],[[0,0],[0]],[[26103384,324],[324]],[[0]],[[6375672]],[[0]],[[1120392]],[[0]],[[133812]],[[0]],[[9720]],[[0]],[[324]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
