/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode079
import Proofs.RadenkovicGutmanD6Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-1944,0],[-1944,-324,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-32076,-28188,0],[-28188,-2808,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-523908,-173664,0],[-173664,-9540,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3806352,-601740,0],[-601740,-16488,0],[0,0]],[[0,0,0],[0,0],[0]],[[-16352820,-1311552,0],[-1311552,-15984],[0]],[[0,0,0],[0,0],[0]],[[-46624644,-1908612,0],[-1908612,-9000],[0]],[[0,0,0],[0,0],[0]],[[-93879864,-1919376,0],[-1919376,-2916],[0]],[[0,0,0],[0,0],[0]],[[-138640176,-1358928,0],[-1358928,-504],[0]],[[0,0,0],[0,0],[0]],[[-153825804,-681480,0],[-681480,-36],[0]],[[0,0],[0]],[[-130180824,-240444],[-240444]],[[0,0],[0]],[[-84735720,-58320],[-58320]],[[0,0],[0]],[[-42529248,-9252],[-9252]],[[0,0],[0]],[[-16405452,-864],[-864]],[[0,0],[0]],[[-4815252,-36],[-36]],[[0]],[[-1055160]],[[0]],[[-167040]],[[0]],[[-18036]],[[0]],[[-1188]],[[0]],[[-36]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
