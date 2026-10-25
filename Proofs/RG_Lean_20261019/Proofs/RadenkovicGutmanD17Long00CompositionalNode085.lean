/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode073
import Proofs.RadenkovicGutmanD17Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1224,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11016,-73440,0],[-73440,-21318,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1322838,-1032750,0],[-1032750,-128860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19759950,-6213636,0],[-6213636,-377638,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-138377280,-21142730,0],[-21142730,-605404,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-581714806,-45449908,0],[-45449908,-562360,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1634045338,-65441466,0],[-65441466,-308516],[0]],[[0,0,0],[0,0],[0]],[[-3254062820,-65267352,0],[-65267352,-98294],[0]],[[0,0,0],[0,0],[0]],[[-4764439040,-45906052,0],[-45906052,-16796],[0]],[[0,0,0],[0,0],[0]],[[-5249902906,-22898456,0],[-22898456,-1190],[0]],[[0,0,0],[0,0],[0]],[[-4417704388,-8043618,0],[-8043618,0],[0]],[[0,0],[0]],[[-2861810260,-1943780],[-1943780]],[[0,0],[0]],[[-1430520760,-307394],[-307394]],[[0,0],[0]],[[-549882986,-28628],[-28628]],[[0,0],[0]],[[-160906258,-1190],[-1190]],[[0,0],[0]],[[-35164500,0],[0]],[[0]],[[-5553560]],[[0]],[[-598366]],[[0]],[[-39338]],[[0]],[[-1190]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
