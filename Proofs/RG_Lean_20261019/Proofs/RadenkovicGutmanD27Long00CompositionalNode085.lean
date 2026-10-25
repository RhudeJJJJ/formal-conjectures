/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode073
import Proofs.RadenkovicGutmanD27Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-1944,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17496,-174960,0],[-174960,-43578,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3063258,-2485890,0],[-2485890,-288900,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-47100690,-15078636,0],[-15078636,-885978,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-333966240,-51631830,0],[-51631830,-1456164,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1414484586,-111531708,0],[-111531708,-1372680,0],[0,0]],[[0,0,0],[0,0],[0]],[[-3993987798,-161194806,0],[-161194806,-759996],[0]],[[0,0,0],[0,0],[0]],[[-7984613340,-161241192,0],[-161241192,-243594],[0]],[[0,0,0],[0,0],[0]],[[-11726255520,-113677452,0],[-113677452,-41796],[0]],[[0,0,0],[0,0],[0]],[[-12952855206,-56812536,0],[-56812536,-2970],[0]],[[0,0,0],[0,0],[0]],[[-10921778748,-19988478,0],[-19988478,0],[0]],[[0,0],[0]],[[-7087299660,-4836780],[-4836780]],[[0,0],[0]],[[-3547881000,-765774],[-765774]],[[0,0],[0]],[[-1365507126,-71388],[-71388]],[[0,0],[0]],[[-400014558,-2970],[-2970]],[[0,0],[0]],[[-87504300,0],[0]],[[0]],[[-13831560]],[[0]],[[-1491426]],[[0]],[[-98118]],[[0]],[[-2970]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
