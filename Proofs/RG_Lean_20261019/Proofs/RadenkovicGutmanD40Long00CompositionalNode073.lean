/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode071
import Proofs.RadenkovicGutmanD40Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-86400,0],[-86400,-17280,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1451520,-1624320,0],[-1624320,-208080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29676240,-13029840,0],[-13029840,-1014240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-269220240,-59116640,0],[-59116640,-2596560,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1441479360,-169550000,0],[-169550000,-3820320,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5112568720,-325837920,0],[-325837920,-3357120,0],[0,0]],[[0,0,0],[0,0],[0]],[[-12783325680,-434388080,0],[-434388080,-1775520],[0]],[[0,0,0],[0,0],[0]],[[-23415012320,-410169920,0],[-410169920,-551760],[0]],[[0,0,0],[0,0],[0]],[[-32219254080,-277214880,0],[-277214880,-92640],[0]],[[0,0,0],[0,0],[0]],[[-33862942640,-134227520,0],[-134227520,-6480],[0]],[[0,0,0],[0,0],[0]],[[-27468003680,-46096880,0],[-46096880,0],[0]],[[0,0],[0]],[[-17285733600,-10946400],[-10946400]],[[0,0],[0]],[[-8442496640,-1707440],[-1707440]],[[0,0],[0]],[[-3184855280,-157280],[-157280]],[[0,0],[0]],[[-917724720,-6480],[-6480]],[[0,0],[0]],[[-198024800,0],[0]],[[0]],[[-30944000]],[[0]],[[-3304400]],[[0]],[[-215600]],[[0]],[[-6480]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
