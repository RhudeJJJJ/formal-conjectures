/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00891 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 841509938662706528425877700608000000000000 235533577971100303044672376130812413739008 322695805032812877806384971776000000000000))
theorem leaf00891_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 841509938662706528425877700608000000000000 235533577971100303044672376130812413739008 322695805032812877806384971776000000000000 raw00891=true := by decide +kernel
#print axioms leaf00891_raw
theorem leaf00891_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00891=true := by decide +kernel
#print axioms leaf00891_rectangular
def affine00891 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00891 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00891_transform : affine00891=(NestedInteger.clearedAll 3 raw00891 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00891_transform
theorem leaf00891_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00891=true := by decide +kernel
#print axioms leaf00891_sign
theorem leaf00891_log : RationalLog.accepts (173729703/1073741824) (-3911435839/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00891_log
def leaf00891 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (729893522933/1000000000000) (173729703/1073741824) (-3911435839/4294967296) 3 8 ![60,0,4] ![(21/320),0,(1/16)] ![(1/640),1,(1/16)] affine00891
theorem leaf00891_checked : FastNestedCellData.accepts 1 2 4 leaf00891=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (729893522933/1000000000000) (173729703/1073741824) (-3911435839/4294967296) 3 8 ![60,0,4] ![(21/320),0,(1/16)] ![(1/640),1,(1/16)] 841509938662706528425877700608000000000000 235533577971100303044672376130812413739008 322695805032812877806384971776000000000000 raw00891 affine00891
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00891_raw leaf00891_rectangular
    leaf00891_transform leaf00891_sign leaf00891_log
#print axioms leaf00891_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
