/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode033
import Proofs.RadenkovicGutmanD11Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,363],[0,363,-198]],[[0,0,0],[0,0,0],[0,0]],[[0,-3267,3267],[-3267,11979,-1991],[3267,-1991]],[[0,0,0],[0,0,0],[0,0]],[[-32967,35937,6831],[35937,17886,-7568],[6831,-7568]],[[0,0,0],[0,0,0],[0,0]],[[-32373,216612,-22374],[216612,-121561,-7865],[-22374,-7865]],[[0,0,0],[0,0,0],[0,0]],[[1019898,-22693,-100859],[-22693,-458854,-3047],[-100859,-3047]],[[0,0,0],[0,0,0],[0,0]],[[3954423,-2613534,-160644],[-2613534,-696300,-396],[-160644,-396]],[[0,0,0],[0,0],[0]],[[-498245,-8640049,-136829],[-8640049,-577566],[-136829]],[[0,0,0],[0,0],[0]],[[-41533822,-14967326,-67826],[-14967326,-281105],[-67826]],[[0,0,0],[0,0],[0]],[[-146119512,-16517303,-19569],[-16517303,-79970],[-19569]],[[0,0,0],[0,0],[0]],[[-288983101,-12400509,-3047],[-12400509,-12309],[-3047]],[[0,0,0],[0,0],[0]],[[-387865676,-6489054,-198],[-6489054,-792],[-198]],[[0,0],[0]],[[-377472612,-2369730],[-2369730]],[[0,0],[0]],[[-274504824,-592328],[-592328]],[[0,0],[0]],[[-151166675,-96602],[-96602]],[[0,0],[0]],[[-63203085,-9262],[-9262]],[[0,0],[0]],[[-19932066,-396],[-396]],[[0]],[[-4662108]],[[0]],[[-783783]],[[0]],[[-89507]],[[0]],[[-6215]],[[0]],[[-198]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
