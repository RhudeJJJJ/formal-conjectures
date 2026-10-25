/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode033
import Proofs.RadenkovicGutmanD14Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,588],[0,588,-336]],[[0,0,0],[0,0,0],[0,0]],[[0,-5292,5292],[-5292,19404,-3500],[5292,-3500]],[[0,0,0],[0,0,0],[0,0]],[[-52164,58212,9828],[58212,24024,-12992],[9828,-12992]],[[0,0,0],[0,0,0],[0,0]],[[-30996,328608,-42840],[328608,-223300,-13412],[-42840,-13412]],[[0,0,0],[0,0,0],[0,0]],[[1717632,-214900,-178220],[-214900,-802648,-5180],[-178220,-5180]],[[0,0,0],[0,0,0],[0,0]],[[6093948,-4871832,-278544],[-4871832,-1201200,-672],[-278544,-672]],[[0,0,0],[0,0],[0]],[[-3776444,-15348004,-235172],[-15348004,-989688],[-235172]],[[0,0,0],[0,0],[0]],[[-78239224,-26129096,-115976],[-26129096,-479780],[-115976]],[[0,0,0],[0,0],[0]],[[-261730224,-28571900,-33348],[-28571900,-136136],[-33348]],[[0,0,0],[0,0],[0]],[[-507982132,-21328020,-5180],[-21328020,-20916],[-5180]],[[0,0,0],[0,0],[0]],[[-674924432,-11116728,-336],[-11116728,-1344],[-336]],[[0,0],[0]],[[-652620528,-4047960],[-4047960]],[[0,0],[0]],[[-472466400,-1009568],[-1009568]],[[0,0],[0]],[[-259314860,-164360],[-164360]],[[0,0],[0]],[[-108140508,-15736],[-15736]],[[0,0],[0]],[[-34033608,-672],[-672]],[[0]],[[-7947072]],[[0]],[[-1334172]],[[0]],[[-152180]],[[0]],[[-10556]],[[0]],[[-336]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
