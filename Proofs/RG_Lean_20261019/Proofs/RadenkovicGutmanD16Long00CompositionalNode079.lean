/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode033
import Proofs.RadenkovicGutmanD16Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,768],[0,768]],[[0,0,0],[0,0,0],[0,0]],[[0,-6912,6912],[-6912,25344,3328],[6912,3328]],[[0,0,0],[0,0,0],[0,0]],[[-103680,76032,48384],[76032,173568,4096],[48384,4096]],[[0,0,0],[0,0,0],[0,0]],[[-656640,1069056,133632],[1069056,466688,1792],[133632,1792]],[[0,0,0],[0,0,0],[0,0]],[[359424,4838144,193792],[4838144,657920,256],[193792,256]],[[0,0,0],[0,0],[0]],[[16912128,11979264,162816],[11979264,537600],[162816]],[[0,0,0],[0,0],[0]],[[80391424,18818816,81664],[18818816,262656],[81664]],[[0,0,0],[0,0],[0]],[[212779520,20022784,24064],[20022784,75520],[24064]],[[0,0,0],[0,0],[0]],[[377687040,14881024,3840],[14881024,11776],[3840]],[[0,0,0],[0,0],[0]],[[482374400,7809792,256],[7809792,768],[256]],[[0,0],[0]],[[458828800,2880000],[2880000]],[[0,0],[0]],[[330814464,729600],[729600]],[[0,0],[0]],[[182126592,120832],[120832]],[[0,0],[0]],[[76514560,11776],[11776]],[[0,0],[0]],[[24323328,512],[512]],[[0]],[[5746176]],[[0]],[[976896]],[[0]],[[112896]],[[0]],[[7936]],[[0]],[[256]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
