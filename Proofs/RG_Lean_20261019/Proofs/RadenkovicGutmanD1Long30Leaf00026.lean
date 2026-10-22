/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00026 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 195175459005851769538070183936000000000000 176686268840492157163269920103378079186944 4174815828845419891849917628416000000000000))
theorem leaf00026_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 195175459005851769538070183936000000000000 176686268840492157163269920103378079186944 4174815828845419891849917628416000000000000 raw00026=true := by decide +kernel
#print axioms leaf00026_raw
theorem leaf00026_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00026=true := by decide +kernel
#print axioms leaf00026_rectangular
def affine00026 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00026 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/16000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00026_transform : affine00026=(NestedInteger.clearedAll 3 raw00026 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/16000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00026_transform
theorem leaf00026_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00026=true := by decide +kernel
#print axioms leaf00026_sign
theorem leaf00026_log : RationalLog.accepts (3730229701/4294967296) (-302739669/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00026_log
def leaf00026 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (21160965667/500000000000) (3730229701/4294967296) (-302739669/4294967296) 1 8 ![60,0,4] ![(21/16000),0,(1/16)] ![(1/16000),1,(1/16)] affine00026
theorem leaf00026_checked : FastNestedCellData.accepts 1 2 4 leaf00026=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (21160965667/500000000000) (3730229701/4294967296) (-302739669/4294967296) 1 8 ![60,0,4] ![(21/16000),0,(1/16)] ![(1/16000),1,(1/16)] 195175459005851769538070183936000000000000 176686268840492157163269920103378079186944 4174815828845419891849917628416000000000000 raw00026 affine00026
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00026_raw leaf00026_rectangular
    leaf00026_transform leaf00026_sign leaf00026_log
#print axioms leaf00026_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
