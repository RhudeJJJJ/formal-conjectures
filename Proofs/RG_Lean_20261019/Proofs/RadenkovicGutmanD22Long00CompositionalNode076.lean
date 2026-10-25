/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode035
import Proofs.RadenkovicGutmanD22Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-4356],[0,-8712],[-4356]],[[0,0,0],[0,0],[0]],[[0,-143748,-37752],[-143748,-75504],[-37752]],[[0,0,0],[0,0],[0]],[[-1176120,-1607364,-128260],[-1607364,-256520],[-128260]],[[0,0,0],[0,0],[0]],[[-16073640,-7679628,-221672],[-7679628,-443344],[-221672]],[[0,0,0],[0,0],[0]],[[-97983864,-20787800,-214896],[-20787800,-429792],[-214896]],[[0,0,0],[0,0],[0]],[[-354682944,-35681932,-121000],[-35681932,-242000],[-121000]],[[0,0,0],[0,0],[0]],[[-856000464,-41109508,-39204],[-41109508,-78408],[-39204]],[[0,0,0],[0,0],[0]],[[-1464640144,-32735824,-6776],[-32735824,-13552],[-6776]],[[0,0,0],[0,0],[0]],[[-1842300504,-18226956,-484],[-18226956,-968],[-484]],[[0,0],[0]],[[-1741411672,-7070756],[-7070756]],[[0,0],[0]],[[-1252460352,-1871144],[-1871144]],[[0,0],[0]],[[-688914952,-321860],[-321860]],[[0,0],[0]],[[-289343912,-32428],[-32428]],[[0,0],[0]],[[-91973552,-1452],[-1452]],[[0]],[[-21727728]],[[0]],[[-3693888]],[[0]],[[-426888]],[[0]],[[-30008]],[[0]],[[-968]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
