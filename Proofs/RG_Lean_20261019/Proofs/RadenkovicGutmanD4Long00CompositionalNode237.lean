/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode234
import Proofs.RadenkovicGutmanD4Long00CompositionalNode236
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e237 : NestedArithmetic.Expr 3 := .plus e234 e236
noncomputable def p237 : NestedHorner.Poly 3 := [[[-16],[0],[0]],[[0,0],[0,0],[0]],[[-528,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-8016,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-74240,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-468960,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2140112,-16,0],[-16,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7291312,-384,0],[-384,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18901888,-4112,0],[-4112,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-37660320,-25920,0],[-25920,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-57858144,-106864,0],[-106864,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-68367024,-302880,0],[-302880,-16,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-61617856,-603968,0],[-603968,-224,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-41724384,-853056,0],[-853056,-1296,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-20722064,-848272,0],[-848272,-4000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7267920,-582912,0],[-582912,-7104,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1691712,-267440,0],[-267440,-7328,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-232848,-77184,0],[-77184,-4240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14256,-12528,0],[-12528,-1248,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-864,0],[-864,-144,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step237 : p237=NestedHorner.add p234 p236 := by decide +kernel
#print axioms step237
theorem h237 : NestedArithmetic.compile e237=p237 := StagedExprCompile.compile_plus e237 e234 e236 p234 p236 p237 rfl h234 h236 step237
#print axioms h237
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
