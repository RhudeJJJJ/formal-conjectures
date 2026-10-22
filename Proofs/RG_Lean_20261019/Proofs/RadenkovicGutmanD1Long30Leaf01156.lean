/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01156 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 23241821271137882131501416448000000000000 29795153455279191056063638532742872825856 369500659510606714104465850368000000000000))
theorem leaf01156_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 23241821271137882131501416448000000000000 29795153455279191056063638532742872825856 369500659510606714104465850368000000000000 raw01156=true := by decide +kernel
#print axioms leaf01156_raw
theorem leaf01156_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01156=true := by decide +kernel
#print axioms leaf01156_rectangular
def affine01156 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01156 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf01156_transform : affine01156=(NestedInteger.clearedAll 3 raw01156 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf01156_transform
theorem leaf01156_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01156=true := by decide +kernel
#print axioms leaf01156_sign
theorem leaf01156_log : RationalLog.accepts (636892017/536870912) (91720339/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01156_log
def leaf01156 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (80636265967/1000000000000) (636892017/536870912) (91720339/1073741824) 0 8 ![60,0,4] ![(13/16),0,(1/2)] ![(1/16),1,(1/4)] affine01156
theorem leaf01156_checked : FastNestedCellData.accepts 1 2 4 leaf01156=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (80636265967/1000000000000) (636892017/536870912) (91720339/1073741824) 0 8 ![60,0,4] ![(13/16),0,(1/2)] ![(1/16),1,(1/4)] 23241821271137882131501416448000000000000 29795153455279191056063638532742872825856 369500659510606714104465850368000000000000 raw01156 affine01156
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01156_raw leaf01156_rectangular
    leaf01156_transform leaf01156_sign leaf01156_log
#print axioms leaf01156_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
