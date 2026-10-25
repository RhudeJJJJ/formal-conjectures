/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode217
import Proofs.RadenkovicGutmanD22Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-968],[0],[0]],[[0,0],[0,0],[0]],[[-30008,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-426888,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-3693888,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-21727728,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-91973552,-1452,0],[-1452,0],[0]],[[0,0,0],[0,0],[0]],[[-289343912,-32428,0],[-32428,0],[0]],[[0,0,0],[0,0],[0]],[[-688914952,-321860,0],[-321860,0],[0]],[[0,0,0],[0,0],[0]],[[-1252460352,-1871144,0],[-1871144,0],[0]],[[0,0,0],[0,0],[0]],[[-1741411672,-7070756,0],[-7070756,0],[0]],[[0,0,0],[0,0],[0]],[[-1842300504,-18226956,-484],[-18226956,-968],[-484]],[[0,0,0],[0,0],[0]],[[-1464640144,-32735824,-6776],[-32735824,-13552],[-6776]],[[0,0,0],[0,0],[0]],[[-856000464,-41109508,-39204],[-41109508,-78408],[-39204]],[[0,0,0],[0,0],[0]],[[-354682944,-35681932,-121000],[-35681932,-242000],[-121000]],[[0,0,0],[0,0],[0]],[[-97983864,-20787800,-214896],[-20787800,-429792],[-214896]],[[0,0,0],[0,0],[0]],[[-16073640,-7679628,-221672],[-7679628,-443344],[-221672]],[[0,0,0],[0,0],[0]],[[-1176120,-1607364,-128260],[-1607364,-256520],[-128260]],[[0,0,0],[0,0],[0]],[[0,-143748,-37752],[-143748,-75504],[-37752]],[[0,0,0],[0,0],[0]],[[0,0,-4356],[0,-8712],[-4356]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
