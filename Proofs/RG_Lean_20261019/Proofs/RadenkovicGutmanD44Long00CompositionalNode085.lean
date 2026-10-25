/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode073
import Proofs.RadenkovicGutmanD44Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-3168,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-28512,-446688,0],[-446688,-97944,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7657848,-6393816,0],[-6393816,-704176,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-120299256,-39006000,0],[-39006000,-2236696,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-860591424,-134152040,0],[-134152040,-3743344,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3664187032,-290759920,0],[-290759920,-3565408,0],[0,0]],[[0,0,0],[0,0],[0]],[[-10383746824,-421314696,0],[-421314696,-1986512],[0]],[[0,0,0],[0,0],[0]],[[-20814422288,-422284896,0],[-422284896,-639320],[0]],[[0,0,0],[0,0],[0]],[[-30631992512,-298194160,0],[-298194160,-110000],[0]],[[0,0,0],[0,0],[0]],[[-33892990120,-149221952,0],[-149221952,-7832],[0]],[[0,0,0],[0,0],[0]],[[-28617927184,-52557384,0],[-52557384,0],[0]],[[0,0],[0]],[[-18592153360,-12729200],[-12729200]],[[0,0],[0]],[[-9316385056,-2016872],[-2016872]],[[0,0],[0]],[[-3588746216,-188144],[-188144]],[[0,0],[0]],[[-1052076520,-7832],[-7832]],[[0,0],[0]],[[-230295120,0],[0]],[[0]],[[-36423200]],[[0]],[[-3929464]],[[0]],[[-258632]],[[0]],[[-7832]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
