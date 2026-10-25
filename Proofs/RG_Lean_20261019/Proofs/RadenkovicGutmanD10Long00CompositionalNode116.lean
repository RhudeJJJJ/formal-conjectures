/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode115
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e116 : NestedArithmetic.Expr 3 := .scaled (-1) e115
noncomputable def p116 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-100]],[[0,0],[0,0,0],[0,0]],[[0,0,-900],[0,0,-1800],[-900,-1800]],[[0,0,0],[0,0,0],[0,0]],[[-8100,-16200,-15900],[-16200,-32400,-4800],[-15900,-4800]],[[0,0,0],[0,0,0],[0,0]],[[-286200,-329400,-69700],[-329400,-172800,-4400],[-69700,-4400]],[[0,0,0],[0,0,0],[0,0]],[[-3782700,-2057400,-143000],[-2057400,-388800,-1600],[-143000,-1600]],[[0,0,0],[0,0,0],[0,0]],[[-24738600,-6633600,-164400],[-6633600,-480000,-200],[-164400,-200]],[[0,0,0],[0,0],[0]],[[-97014100,-13146200,-113600],[-13146200,-354400],[-113600]],[[0,0,0],[0,0],[0]],[[-253666000,-17375000,-48100],[-17375000,-160000],[-48100]],[[0,0,0],[0,0],[0]],[[-470654200,-15979600,-12200],[-15979600,-43200],[-12200]],[[0,0,0],[0,0],[0]],[[-644057800,-10443200,-1700],[-10443200,-6400],[-1700]],[[0,0,0],[0,0],[0]],[[-666131200,-4879000,-100],[-4879000,-400],[-100]],[[0,0],[0]],[[-528632000,-1617000],[-1617000]],[[0,0],[0]],[[-324496000,-371000],[-371000]],[[0,0],[0]],[[-154398200,-56000],[-56000]],[[0,0],[0]],[[-56730100,-5000],[-5000]],[[0,0],[0]],[[-15927600,-200],[-200]],[[0]],[[-3351000]],[[0]],[[-511000]],[[0]],[[-53300]],[[0]],[[-3400]],[[0]],[[-100]]]
theorem step116 : p116=NestedHorner.scale (-1) p115 := by decide +kernel
#print axioms step116
theorem h116 : NestedArithmetic.compile e116=p116 := StagedExprCompile.compile_scaled (-1) e116 e115 p115 p116 rfl h115 step116
#print axioms h116
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
