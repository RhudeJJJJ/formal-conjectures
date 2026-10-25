/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode033
import Proofs.RadenkovicGutmanD22Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1452],[0,1452]],[[0,0,0],[0,0,0],[0,0]],[[0,-13068,13068],[-13068,47916,6292],[13068,6292]],[[0,0,0],[0,0,0],[0,0]],[[-196020,143748,91476],[143748,328152,7744],[91476,7744]],[[0,0,0],[0,0,0],[0,0]],[[-1241460,2021184,252648],[2021184,882332,3388],[252648,3388]],[[0,0,0],[0,0,0],[0,0]],[[679536,9147116,366388],[9147116,1243880,484],[366388,484]],[[0,0,0],[0,0],[0]],[[31974492,22648296,307824],[22648296,1016400],[307824]],[[0,0,0],[0,0],[0]],[[151990036,35579324,154396],[35579324,496584],[154396]],[[0,0,0],[0,0],[0]],[[402286280,37855576,45496],[37855576,142780],[45496]],[[0,0,0],[0,0],[0]],[[714064560,28134436,7260],[28134436,22264],[7260]],[[0,0,0],[0,0],[0]],[[911989100,14765388,484],[14765388,1452],[484]],[[0,0],[0]],[[867473200,5445000],[5445000]],[[0,0],[0]],[[625446096,1379400],[1379400]],[[0,0],[0]],[[344333088,228448],[228448]],[[0,0],[0]],[[144660340,22264],[22264]],[[0,0],[0]],[[45986292,968],[968]],[[0]],[[10863864]],[[0]],[[1846944]],[[0]],[[213444]],[[0]],[[15004]],[[0]],[[484]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
