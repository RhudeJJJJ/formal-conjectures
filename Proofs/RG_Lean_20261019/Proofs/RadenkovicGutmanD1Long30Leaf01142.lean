/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01142 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1993971893732673507599788802048000000000000 2540872880143399044194868019396449052655616 23506265003612138948021371011072000000000000))
theorem leaf01142_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1993971893732673507599788802048000000000000 2540872880143399044194868019396449052655616 23506265003612138948021371011072000000000000 raw01142=true := by decide +kernel
#print axioms leaf01142_raw
theorem leaf01142_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01142=true := by decide +kernel
#print axioms leaf01142_rectangular
def affine01142 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01142 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01142_transform : affine01142=(NestedInteger.clearedAll 3 raw01142 (IntegerComputedClassCell.leftNumerator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(15/16),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01142_transform
theorem leaf01142_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01142=true := by decide +kernel
#print axioms leaf01142_sign
theorem leaf01142_log : RationalLog.accepts (4939095069/4294967296) (300085475/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01142_log
def leaf01142 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (108093432953/1000000000000) (4939095069/4294967296) (300085475/4294967296) 0 8 ![60,0,4] ![(15/16),0,(3/4)] ![(1/16),1,(1/8)] affine01142
theorem leaf01142_checked : FastNestedCellData.accepts 1 2 4 leaf01142=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (108093432953/1000000000000) (4939095069/4294967296) (300085475/4294967296) 0 8 ![60,0,4] ![(15/16),0,(3/4)] ![(1/16),1,(1/8)] 1993971893732673507599788802048000000000000 2540872880143399044194868019396449052655616 23506265003612138948021371011072000000000000 raw01142 affine01142
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01142_raw leaf01142_rectangular
    leaf01142_transform leaf01142_sign leaf01142_log
#print axioms leaf01142_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
