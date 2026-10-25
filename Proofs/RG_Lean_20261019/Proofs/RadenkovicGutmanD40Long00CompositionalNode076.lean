/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode035
import Proofs.RadenkovicGutmanD40Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-14400],[0,-28800],[-14400]],[[0,0,0],[0,0],[0]],[[0,-475200,-124800],[-475200,-249600],[-124800]],[[0,0,0],[0,0],[0]],[[-3888000,-5313600,-424000],[-5313600,-848000],[-424000]],[[0,0,0],[0,0],[0]],[[-53136000,-25387200,-732800],[-25387200,-1465600],[-732800]],[[0,0,0],[0,0],[0]],[[-323913600,-68720000,-710400],[-68720000,-1420800],[-710400]],[[0,0,0],[0,0],[0]],[[-1172505600,-117956800,-400000],[-117956800,-800000],[-400000]],[[0,0,0],[0,0],[0]],[[-2829753600,-135899200,-129600],[-135899200,-259200],[-129600]],[[0,0,0],[0,0],[0]],[[-4841785600,-108217600,-22400],[-108217600,-44800],[-22400]],[[0,0,0],[0,0],[0]],[[-6090249600,-60254400,-1600],[-60254400,-3200],[-1600]],[[0,0],[0]],[[-5756732800,-23374400],[-23374400]],[[0,0],[0]],[[-4140364800,-6185600],[-6185600]],[[0,0],[0]],[[-2277404800,-1064000],[-1064000]],[[0,0],[0]],[[-956508800,-107200],[-107200]],[[0,0],[0]],[[-304044800,-4800],[-4800]],[[0]],[[-71827200]],[[0]],[[-12211200]],[[0]],[[-1411200]],[[0]],[[-99200]],[[0]],[[-3200]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
