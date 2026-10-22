/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00064 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 30327637565621661094513737728000000000000 29851137306976601903871268998426277183488 4539228360760658615048375107584000000000000))
theorem leaf00064_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 30327637565621661094513737728000000000000 29851137306976601903871268998426277183488 4539228360760658615048375107584000000000000 raw00064=true := by decide +kernel
#print axioms leaf00064_raw
theorem leaf00064_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00064=true := by decide +kernel
#print axioms leaf00064_rectangular
def affine00064 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00064 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00064_transform : affine00064=(NestedInteger.clearedAll 3 raw00064 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00064_transform
theorem leaf00064_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00064=true := by decide +kernel
#print axioms leaf00064_sign
theorem leaf00064_log : RationalLog.accepts (2099933219/2147483648) (-48084809/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00064_log
def leaf00064 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6576258107/1000000000000) (2099933219/2147483648) (-48084809/4294967296) 1 8 ![60,0,4] ![(7/4000),0,(1/2)] ![(1/16000),1,(1/2)] affine00064
theorem leaf00064_checked : FastNestedCellData.accepts 1 2 4 leaf00064=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6576258107/1000000000000) (2099933219/2147483648) (-48084809/4294967296) 1 8 ![60,0,4] ![(7/4000),0,(1/2)] ![(1/16000),1,(1/2)] 30327637565621661094513737728000000000000 29851137306976601903871268998426277183488 4539228360760658615048375107584000000000000 raw00064 affine00064
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00064_raw leaf00064_rectangular
    leaf00064_transform leaf00064_sign leaf00064_log
#print axioms leaf00064_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
