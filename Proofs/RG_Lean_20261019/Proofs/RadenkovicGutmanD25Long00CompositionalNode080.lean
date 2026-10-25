/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode035
import Proofs.RadenkovicGutmanD25Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1875],[0,-1875]],[[0,0,0],[0,0,0],[0,0]],[[0,-16875,-16875],[-16875,-67500,-8125],[-16875,-8125]],[[0,0,0],[0,0,0],[0,0]],[[-303750,-675000,-118125],[-675000,-472500,-10000],[-118125,-10000]],[[0,0,0],[0,0,0],[0,0]],[[-7492500,-5625000,-326250],[-5625000,-1305000,-4375],[-326250,-4375]],[[0,0,0],[0,0,0],[0,0]],[[-66960000,-22258750,-473125],[-22258750,-1892500,-625],[-473125,-625]],[[0,0,0],[0,0],[0]],[[-325192500,-52016250,-397500],[-52016250,-1590000],[-397500]],[[0,0,0],[0,0],[0]],[[-1005723750,-79080000,-199375],[-79080000,-797500],[-199375]],[[0,0,0],[0,0],[0]],[[-2149340000,-82206250,-58750],[-82206250,-235000],[-58750]],[[0,0,0],[0,0],[0]],[[-3329035000,-59923125,-9375],[-59923125,-37500],[-9375]],[[0,0,0],[0,0],[0]],[[-3848258750,-30898125,-625],[-30898125,-2500],[-625]],[[0,0],[0]],[[-3380271250,-11205625],[-11205625]],[[0,0],[0]],[[-2278758750,-2793750],[-2793750]],[[0,0],[0]],[[-1183000000,-455625],[-455625]],[[0,0],[0]],[[-471620000,-43750],[-43750]],[[0,0],[0]],[[-142981250,-1875],[-1875]],[[0]],[[-32347500]],[[0]],[[-5285000]],[[0]],[[-588750]],[[0]],[[-40000]],[[0]],[[-1250]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
