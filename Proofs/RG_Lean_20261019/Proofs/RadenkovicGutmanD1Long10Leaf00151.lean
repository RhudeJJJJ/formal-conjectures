/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00151 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2747289823660470041107138347008000000000000 1987795219826398873231182027393073302994944 13347099157606947421408028786688000000000000))
theorem leaf00151_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2747289823660470041107138347008000000000000 1987795219826398873231182027393073302994944 13347099157606947421408028786688000000000000 raw00151=true := by decide +kernel
#print axioms leaf00151_raw
theorem leaf00151_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00151=true := by decide +kernel
#print axioms leaf00151_rectangular
def affine00151 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00151 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00151_transform : affine00151=(NestedInteger.clearedAll 3 raw00151 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00151_transform
theorem leaf00151_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00151=true := by decide +kernel
#print axioms leaf00151_sign
theorem leaf00151_log : RationalLog.accepts (2704787331/4294967296) (-993040825/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00151_log
def leaf00151 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (148930879763/1000000000000) (2704787331/4294967296) (-993040825/4294967296) 1 8 ![52,0,4] ![(1/50),0,(1/4)] ![(3/6400),1,(1/4)] affine00151
theorem leaf00151_checked : FastNestedCellData.accepts 1 0 4 leaf00151=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (148930879763/1000000000000) (2704787331/4294967296) (-993040825/4294967296) 1 8 ![52,0,4] ![(1/50),0,(1/4)] ![(3/6400),1,(1/4)] 2747289823660470041107138347008000000000000 1987795219826398873231182027393073302994944 13347099157606947421408028786688000000000000 raw00151 affine00151
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00151_raw leaf00151_rectangular
    leaf00151_transform leaf00151_sign leaf00151_log
#print axioms leaf00151_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
