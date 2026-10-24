/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode078
import Proofs.RadenkovicGutmanD4Long00CompositionalNode079
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .plus e078 e079
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-864,0],[-864,-144,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14256,-12528,0],[-12528,-1248,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-232848,-77184,0],[-77184,-4240,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1691712,-267440,0],[-267440,-7328,0],[0,0]],[[0,0,0],[0,0],[0]],[[-7267920,-582912,0],[-582912,-7104],[0]],[[0,0,0],[0,0],[0]],[[-20722064,-848272,0],[-848272,-4000],[0]],[[0,0,0],[0,0],[0]],[[-41724384,-853056,0],[-853056,-1296],[0]],[[0,0,0],[0,0],[0]],[[-61617856,-603968,0],[-603968,-224],[0]],[[0,0,0],[0,0],[0]],[[-68367024,-302880,0],[-302880,-16],[0]],[[0,0],[0]],[[-57858144,-106864],[-106864]],[[0,0],[0]],[[-37660320,-25920],[-25920]],[[0,0],[0]],[[-18901888,-4112],[-4112]],[[0,0],[0]],[[-7291312,-384],[-384]],[[0,0],[0]],[[-2140112,-16],[-16]],[[0]],[[-468960]],[[0]],[[-74240]],[[0]],[[-8016]],[[0]],[[-528]],[[0]],[[-16]]]
theorem step080 : p080=NestedHorner.add p078 p079 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_plus e080 e078 e079 p078 p079 p080 rfl h078 h079 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
