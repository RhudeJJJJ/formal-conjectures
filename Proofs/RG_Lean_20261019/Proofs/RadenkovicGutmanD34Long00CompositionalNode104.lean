/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode092
import Proofs.RadenkovicGutmanD34Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2448,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22032,-22032,0],[-22032,-20604,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-574668,-244188,0],[-244188,-66776,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5583276,-1149336,0],[-1149336,-106556,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29438016,-3034500,0],[-3034500,-89624,0],[0,0]],[[0,0,0],[0,0],[0]],[[-97780124,-5000312,0],[-5000312,-37808],[0]],[[0,0,0],[0,0],[0]],[[-221003604,-5390292,0],[-5390292,-5032],[0]],[[0,0,0],[0,0],[0]],[[-355263144,-3843632,0],[-3843632,1700],[0]],[[0,0,0],[0,0],[0]],[[-416544064,-1760792,0],[-1760792,680],[0]],[[0,0,0],[0,0],[0]],[[-360360356,-455872,0],[-455872,68],[0]],[[0,0],[0]],[[-229624168,-23732],[-23732]],[[0,0],[0]],[[-105571496,25160],[25160]],[[0,0],[0]],[[-32899760,8636],[8636]],[[0,0],[0]],[[-5516772,1224],[1224]],[[0,0],[0]],[[355708,68],[68]],[[0]],[[488376]],[[0]],[[139536]],[[0]],[[21556]],[[0]],[[1836]],[[0]],[[68]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
