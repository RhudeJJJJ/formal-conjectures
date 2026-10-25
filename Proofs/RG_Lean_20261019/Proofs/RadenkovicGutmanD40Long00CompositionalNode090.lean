/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode035
import Proofs.RadenkovicGutmanD40Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4800],[0,-4800]],[[0,0,0],[0,0,0],[0,0]],[[0,-43200,-72000],[-43200,-230400,-21040],[-72000,-21040]],[[0,0,0],[0,0,0],[0,0]],[[-777600,-2680560,-554160],[-2680560,-1717440,-26640],[-554160,-26640]],[[0,0,0],[0,0,0],[0,0]],[[-26995680,-25113600,-1698320],[-25113600,-5097280,-12480],[-1698320,-12480]],[[0,0,0],[0,0,0],[0,0]],[[-278648640,-108476800,-2718560],[-108476800,-7943040,-2160],[-2718560,-2160]],[[0,0,0],[0,0,0],[0,0]],[[-1488890880,-273450720,-2498960],[-273450720,-7154240,-80],[-2498960,-80]],[[0,0,0],[0,0],[0]],[[-4961288640,-445016480,-1361280],[-445016480,-3845120],[-1361280]],[[0,0,0],[0,0],[0]],[[-11290550240,-492368640,-435120],[-492368640,-1222080],[-435120]],[[0,0,0],[0,0],[0]],[[-18481016320,-380360800,-76320],[-380360800,-215680],[-76320]],[[0,0,0],[0,0],[0]],[[-22458158080,-207278160,-6000],[-207278160,-17600],[-6000]],[[0,0,0],[0,0],[0]],[[-20659537120,-79390160,-80],[-79390160,-320],[-80]],[[0,0],[0]],[[-14547026720,-20957520],[-20957520]],[[0,0],[0]],[[-7874970720,-3652000],[-3652000]],[[0,0],[0]],[[-3271788800,-384720],[-384720]],[[0,0],[0]],[[-1034488960,-20000],[-20000]],[[0,0],[0]],[[-244765600,-240],[-240]],[[0]],[[-42092480]],[[0]],[[-5006080]],[[0]],[[-376160]],[[0]],[[-14720]],[[0]],[[-160]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
