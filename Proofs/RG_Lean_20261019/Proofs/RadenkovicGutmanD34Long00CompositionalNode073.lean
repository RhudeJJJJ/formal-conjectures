/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode071
import Proofs.RadenkovicGutmanD34Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-62424,0],[-62424,-12852,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1052028,-1176876,0],[-1176876,-153612,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21528936,-9452340,0],[-9452340,-744396,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-195392628,-42902900,0],[-42902900,-1897404,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1046314164,-123045932,0],[-123045932,-2782968,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3710813176,-236418252,0],[-236418252,-2440248,0],[0,0]],[[0,0,0],[0,0],[0]],[[-9277015668,-315091532,0],[-315091532,-1288668],[0]],[[0,0,0],[0,0],[0]],[[-16989189224,-297437984,0],[-297437984,-400044],[0]],[[0,0,0],[0,0],[0]],[[-23372175756,-200968560,0],[-200968560,-67116],[0]],[[0,0,0],[0,0],[0]],[[-24559091684,-97283996,0],[-97283996,-4692],[0]],[[0,0,0],[0,0],[0]],[[-19916868704,-33401804,0],[-33401804,0],[0]],[[0,0],[0]],[[-12531198168,-7930092],[-7930092]],[[0,0],[0]],[[-6119161628,-1236716],[-1236716]],[[0,0],[0]],[[-2307983648,-113900],[-113900]],[[0,0],[0]],[[-664941060,-4692],[-4692]],[[0,0],[0]],[[-143457560,0],[0]],[[0]],[[-22413956]],[[0]],[[-2393192]],[[0]],[[-156128]],[[0]],[[-4692]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
