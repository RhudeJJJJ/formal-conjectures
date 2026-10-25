/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode071
import Proofs.RadenkovicGutmanD27Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-39366,0],[-39366,-8505,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-667035,-745767,0],[-745767,-100440,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13672395,-6002586,0],[-6002586,-482085,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-124179318,-27263871,0],[-27263871,-1219860,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-665110845,-78190758,0],[-78190758,-1779840,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2358633627,-150181101,0],[-150181101,-1554930,0],[0,0]],[[0,0,0],[0,0],[0]],[[-5895055044,-200062170,0],[-200062170,-819045],[0]],[[0,0,0],[0,0],[0]],[[-10792076904,-188759484,0],[-188759484,-253800],[0]],[[0,0,0],[0,0],[0]],[[-14841228051,-127477422,0],[-127477422,-42525],[0]],[[0,0,0],[0,0],[0]],[[-15589016892,-61681527,0],[-61681527,-2970],[0]],[[0,0,0],[0,0],[0]],[[-12637677078,-21169458,0],[-21169458,0],[0]],[[0,0],[0]],[[-7948516932,-5024133],[-5024133]],[[0,0],[0]],[[-3880091403,-783270],[-783270]],[[0,0],[0]],[[-1463015979,-72117],[-72117]],[[0,0],[0]],[[-421381548,-2970],[-2970]],[[0,0],[0]],[[-90886860,0],[0]],[[0]],[[-14196789]],[[0]],[[-1515483]],[[0]],[[-98847]],[[0]],[[-2970]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
