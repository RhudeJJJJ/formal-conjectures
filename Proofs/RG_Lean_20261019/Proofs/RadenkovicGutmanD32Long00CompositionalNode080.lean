/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode035
import Proofs.RadenkovicGutmanD32Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3072],[0,-3072]],[[0,0,0],[0,0,0],[0,0]],[[0,-27648,-27648],[-27648,-110592,-13312],[-27648,-13312]],[[0,0,0],[0,0,0],[0,0]],[[-497664,-1105920,-193536],[-1105920,-774144,-16384],[-193536,-16384]],[[0,0,0],[0,0,0],[0,0]],[[-12275712,-9216000,-534528],[-9216000,-2138112,-7168],[-534528,-7168]],[[0,0,0],[0,0,0],[0,0]],[[-109707264,-36468736,-775168],[-36468736,-3100672,-1024],[-775168,-1024]],[[0,0,0],[0,0],[0]],[[-532795392,-85223424,-651264],[-85223424,-2605056],[-651264]],[[0,0,0],[0,0],[0]],[[-1647777792,-129564672,-326656],[-129564672,-1306624],[-326656]],[[0,0,0],[0,0],[0]],[[-3521478656,-134686720,-96256],[-134686720,-385024],[-96256]],[[0,0,0],[0,0],[0]],[[-5454290944,-98178048,-15360],[-98178048,-61440],[-15360]],[[0,0,0],[0,0],[0]],[[-6304987136,-50623488,-1024],[-50623488,-4096],[-1024]],[[0,0],[0]],[[-5538236416,-18359296],[-18359296]],[[0,0],[0]],[[-3733518336,-4577280],[-4577280]],[[0,0],[0]],[[-1938227200,-746496],[-746496]],[[0,0],[0]],[[-772702208,-71680],[-71680]],[[0,0],[0]],[[-234260480,-3072],[-3072]],[[0]],[[-52998144]],[[0]],[[-8658944]],[[0]],[[-964608]],[[0]],[[-65536]],[[0]],[[-2048]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
