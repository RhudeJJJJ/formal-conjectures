/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01162 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 803669614694083919515484160000000000 1028571464920686650954869402540965888 14409758629184955410808832000000000000))
theorem leaf01162_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 803669614694083919515484160000000000 1028571464920686650954869402540965888 14409758629184955410808832000000000000 raw01162=true := by decide +kernel
#print axioms leaf01162_raw
theorem leaf01162_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01162=true := by decide +kernel
#print axioms leaf01162_rectangular
def affine01162 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01162 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01162_transform : affine01162=(NestedInteger.clearedAll 3 raw01162 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01162_transform
theorem leaf01162_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01162=true := by decide +kernel
#print axioms leaf01162_sign
theorem leaf01162_log : RationalLog.accepts (40083275/33554432) (190900783/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01162_log
def leaf01162 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (35690100417/500000000000) (40083275/33554432) (190900783/2147483648) 0 8 ![60,0,4] ![(3/4),0,(3/4)] ![(1/16),1,(1/8)] affine01162
theorem leaf01162_checked : FastNestedCellData.accepts 1 2 4 leaf01162=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (35690100417/500000000000) (40083275/33554432) (190900783/2147483648) 0 8 ![60,0,4] ![(3/4),0,(3/4)] ![(1/16),1,(1/8)] 803669614694083919515484160000000000 1028571464920686650954869402540965888 14409758629184955410808832000000000000 raw01162 affine01162
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01162_raw leaf01162_rectangular
    leaf01162_transform leaf01162_sign leaf01162_log
#print axioms leaf01162_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
