/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode033
import Proofs.RadenkovicGutmanD39Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4563],[0,4563,-2886]],[[0,0,0],[0,0,0],[0,0]],[[0,-41067,41067],[-41067,150579,-32175],[41067,-32175]],[[0,0,0],[0,0,0],[0,0]],[[-382239,451737,53703],[451737,96174,-114192],[53703,-114192]],[[0,0,0],[0,0,0],[0,0]],[[150579,2143908,-452790],[2143908,-2214225,-116337],[-452790,-116337]],[[0,0,0],[0,0,0],[0,0]],[[14525082,-4916925,-1653795],[-4916925,-7311798,-44655],[-1653795,-44655]],[[0,0,0],[0,0,0],[0,0]],[[41607423,-49449582,-2495844],[-49449582,-10658700,-5772],[-2495844,-5772]],[[0,0,0],[0,0],[0]],[[-83466669,-143773929,-2071797],[-143773929,-8667438],[-2071797]],[[0,0,0],[0,0],[0]],[[-807084174,-237140046,-1011426],[-237140046,-4168905],[-1011426]],[[0,0,0],[0,0],[0]],[[-2487818424,-254858175,-288873],[-254858175,-1176786],[-288873]],[[0,0,0],[0,0],[0]],[[-4669398357,-188149845,-44655],[-188149845,-180141],[-44655]],[[0,0,0],[0,0],[0]],[[-6088367532,-97312878,-2886],[-97312878,-11544],[-2886]],[[0,0],[0]],[[-5815533828,-35232210],[-35232210]],[[0,0],[0]],[[-4173756600,-8748168],[-8748168]],[[0,0],[0]],[[-2275898235,-1419210],[-1419210]],[[0,0],[0]],[[-944289333,-135486],[-135486]],[[0,0],[0]],[[-295971858,-5772],[-5772]],[[0]],[[-68879772]],[[0]],[[-11531247]],[[0]],[[-1312155]],[[0]],[[-90831]],[[0]],[[-2886]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
