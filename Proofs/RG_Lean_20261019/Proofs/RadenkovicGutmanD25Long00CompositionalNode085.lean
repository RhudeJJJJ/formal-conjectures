/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode073
import Proofs.RadenkovicGutmanD25Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1800,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16200,-151200,0],[-151200,-38550,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2658150,-2145150,0],[-2145150,-251900,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-40701150,-12996900,0],[-12996900,-767350,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-288081600,-44464250,0],[-44464250,-1256700,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1218858950,-95983700,0],[-95983700,-1182200,0],[0,0]],[[0,0,0],[0,0],[0]],[[-3439111050,-138651050,0],[-138651050,-653700],[0]],[[0,0,0],[0,0],[0]],[[-6871605700,-138634200,0],[-138634200,-209350],[0]],[[0,0,0],[0,0],[0]],[[-10087420800,-97707300,0],[-97707300,-35900],[0]],[[0,0,0],[0,0],[0]],[[-11138796650,-48818200,0],[-48818200,-2550],[0]],[[0,0,0],[0,0],[0]],[[-9389531300,-17172050,0],[-17172050,0],[0]],[[0,0],[0]],[[-6091560500,-4154500],[-4154500]],[[0,0],[0]],[[-3048801400,-657650],[-657650]],[[0,0],[0]],[[-1173217050,-61300],[-61300]],[[0,0],[0]],[[-343632450,-2550],[-2550]],[[0,0],[0]],[[-75160500,0],[0]],[[0]],[[-11879000]],[[0]],[[-1280750]],[[0]],[[-84250]],[[0]],[[-2550]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
