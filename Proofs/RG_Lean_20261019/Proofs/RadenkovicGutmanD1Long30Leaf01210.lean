/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01210 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 3787116140974986279086194688000000000000 4326820142597516112904565637870470037504 329306245390355534441927933952000000000000))
theorem leaf01210_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 3787116140974986279086194688000000000000 4326820142597516112904565637870470037504 329306245390355534441927933952000000000000 raw01210=true := by decide +kernel
#print axioms leaf01210_raw
theorem leaf01210_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01210=true := by decide +kernel
#print axioms leaf01210_rectangular
def affine01210 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01210 (IntegerComputedClassCell.leftNumerator ![(21/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf01210_transform : affine01210=(NestedInteger.clearedAll 3 raw01210 (IntegerComputedClassCell.leftNumerator ![(21/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01210_transform
theorem leaf01210_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01210=true := by decide +kernel
#print axioms leaf01210_sign
theorem leaf01210_log : RationalLog.accepts (4843406959/4294967296) (32259083/536870912) 0 8=true := by decide +kernel
#print axioms leaf01210_log
def leaf01210 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1642399819/125000000000) (4843406959/4294967296) (32259083/536870912) 0 8 ![60,0,4] ![(21/64),0,0] ![(1/64),1,(1/2)] affine01210
theorem leaf01210_checked : FastNestedCellData.accepts 1 2 4 leaf01210=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1642399819/125000000000) (4843406959/4294967296) (32259083/536870912) 0 8 ![60,0,4] ![(21/64),0,0] ![(1/64),1,(1/2)] 3787116140974986279086194688000000000000 4326820142597516112904565637870470037504 329306245390355534441927933952000000000000 raw01210 affine01210
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01210_raw leaf01210_rectangular
    leaf01210_transform leaf01210_sign leaf01210_log
#print axioms leaf01210_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
