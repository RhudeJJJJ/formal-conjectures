/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01269 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 352930278789969796105502720000000000 373995671888120497995559129250267136 122173607271112610675561594880000000000))
theorem leaf01269_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 352930278789969796105502720000000000 373995671888120497995559129250267136 122173607271112610675561594880000000000 raw01269=true := by decide +kernel
#print axioms leaf01269_raw
theorem leaf01269_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01269=true := by decide +kernel
#print axioms leaf01269_rectangular
def affine01269 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01269 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/16),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01269_transform : affine01269=(NestedInteger.clearedAll 3 raw01269 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/16),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01269_transform
theorem leaf01269_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01269=true := by decide +kernel
#print axioms leaf01269_sign
theorem leaf01269_log : RationalLog.accepts (2268715817/2147483648) (58966885/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01269_log
def leaf01269 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (15305911/5000000000) (2268715817/2147483648) (58966885/2147483648) 0 8 ![60,0,4] ![(3/16),0,(15/16)] ![(1/128),1,(1/16)] affine01269
theorem leaf01269_checked : FastNestedCellData.accepts 1 2 4 leaf01269=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (15305911/5000000000) (2268715817/2147483648) (58966885/2147483648) 0 8 ![60,0,4] ![(3/16),0,(15/16)] ![(1/128),1,(1/16)] 352930278789969796105502720000000000 373995671888120497995559129250267136 122173607271112610675561594880000000000 raw01269 affine01269
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01269_raw leaf01269_rectangular
    leaf01269_transform leaf01269_sign leaf01269_log
#print axioms leaf01269_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
