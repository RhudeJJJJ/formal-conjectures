/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode099
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .scaled (-1) e099
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1734],[0,-1734,510]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-20808],[0,-71451,1564],[-20808,1564]],[[0,0,0],[0,0,0],[0,0]],[[-75735,-581553,-113934],[-581553,-353328,14790],[-113934,14790]],[[0,0,0],[0,0,0],[0,0]],[[-5147685,-5142636,-240992],[-5142636,-614431,17850],[-240992,17850]],[[0,0,0],[0,0,0],[0,0]],[[-55952100,-19857411,-224298],[-19857411,-288660,7344],[-224298,7344]],[[0,0,0],[0,0,0],[0,0]],[[-294432639,-43813046,-37978],[-43813046,444856,986],[-37978,986]],[[0,0,0],[0,0],[0]],[[-946793495,-60587405,101354],[-60587405,747762],[101354]],[[0,0,0],[0,0],[0]],[[-2055495568,-53777800,92004],[-53777800,482545],[92004]],[[0,0,0],[0,0],[0]],[[-3173187020,-29333738,35122],[-29333738,161568],[35122]],[[0,0,0],[0,0],[0]],[[-3581848405,-7562212,6494],[-7562212,27761],[6494]],[[0,0,0],[0,0],[0]],[[-2992509184,1434953,476],[1434953,1938],[476]],[[0,0],[0]],[[-1846534866,2020620],[2020620]],[[0,0],[0]],[[-823298236,801941],[801941]],[[0,0],[0]],[[-248277537,170442],[170442]],[[0,0],[0]],[[-39415775,19533],[19533]],[[0,0],[0]],[[3343560,952],[952]],[[0]],[[3724360]],[[0]],[[1029061]],[[0]],[[155669]],[[0]],[[13039]],[[0]],[[476]]]
theorem step103 : p103=NestedHorner.scale (-1) p099 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_scaled (-1) e103 e099 p099 p103 rfl h099 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
