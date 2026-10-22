/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01263 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 49225211442945662702007091200000000000 52376308037072153964633874788721360896 15334055989237057888584728576000000000000))
theorem leaf01263_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 49225211442945662702007091200000000000 52376308037072153964633874788721360896 15334055989237057888584728576000000000000 raw01263=true := by decide +kernel
#print axioms leaf01263_raw
theorem leaf01263_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01263=true := by decide +kernel
#print axioms leaf01263_rectangular
def affine01263 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01263 (IntegerComputedClassCell.leftNumerator ![(25/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(25/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(25/128),0,(7/8)] ![(1/128),1,(1/16)]))
theorem leaf01263_transform : affine01263=(NestedInteger.clearedAll 3 raw01263 (IntegerComputedClassCell.leftNumerator ![(25/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(25/128),0,(7/8)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(25/128),0,(7/8)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01263_transform
theorem leaf01263_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01263=true := by decide +kernel
#print axioms leaf01263_sign
theorem leaf01263_log : RationalLog.accepts (1138587145/1073741824) (31481341/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01263_log
def leaf01263 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (853921299/250000000000) (1138587145/1073741824) (31481341/1073741824) 0 8 ![60,0,4] ![(25/128),0,(7/8)] ![(1/128),1,(1/16)] affine01263
theorem leaf01263_checked : FastNestedCellData.accepts 1 2 4 leaf01263=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (853921299/250000000000) (1138587145/1073741824) (31481341/1073741824) 0 8 ![60,0,4] ![(25/128),0,(7/8)] ![(1/128),1,(1/16)] 49225211442945662702007091200000000000 52376308037072153964633874788721360896 15334055989237057888584728576000000000000 raw01263 affine01263
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01263_raw leaf01263_rectangular
    leaf01263_transform leaf01263_sign leaf01263_log
#print axioms leaf01263_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
