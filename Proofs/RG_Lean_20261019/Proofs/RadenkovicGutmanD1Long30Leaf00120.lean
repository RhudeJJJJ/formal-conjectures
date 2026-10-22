/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00120 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4737708603372749437756405448704000000000000 593010562268147594567370906984222031872 2308946157511591959239589888000000000000))
theorem leaf00120_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4737708603372749437756405448704000000000000 593010562268147594567370906984222031872 2308946157511591959239589888000000000000 raw00120=true := by decide +kernel
#print axioms leaf00120_raw
theorem leaf00120_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00120=true := by decide +kernel
#print axioms leaf00120_rectangular
def affine00120 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00120 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/4000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00120_transform : affine00120=(NestedInteger.clearedAll 3 raw00120 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/4000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00120_transform
theorem leaf00120_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00120=true := by decide +kernel
#print axioms leaf00120_sign
theorem leaf00120_log : RationalLog.accepts (427737/4294967296) (-19787872557/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00120_log
def leaf00120 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (256831698019/1000000000000) (427737/4294967296) (-19787872557/4294967296) 14 8 ![60,0,4] ![(11/4000),0,0] ![(3/32000),1,(1/16)] affine00120
theorem leaf00120_checked : FastNestedCellData.accepts 1 2 4 leaf00120=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (256831698019/1000000000000) (427737/4294967296) (-19787872557/4294967296) 14 8 ![60,0,4] ![(11/4000),0,0] ![(3/32000),1,(1/16)] 4737708603372749437756405448704000000000000 593010562268147594567370906984222031872 2308946157511591959239589888000000000000 raw00120 affine00120
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00120_raw leaf00120_rectangular
    leaf00120_transform leaf00120_sign leaf00120_log
#print axioms leaf00120_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
