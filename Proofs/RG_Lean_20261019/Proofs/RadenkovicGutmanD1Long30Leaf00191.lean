/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00191 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 36907578589405101234537365504000000000000 27636045767666932043095380632399882747904 215824179515455844597989638144000000000000))
theorem leaf00191_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 36907578589405101234537365504000000000000 27636045767666932043095380632399882747904 215824179515455844597989638144000000000000 raw00191=true := by decide +kernel
#print axioms leaf00191_raw
theorem leaf00191_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00191=true := by decide +kernel
#print axioms leaf00191_rectangular
def affine00191 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00191 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/3200),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00191_transform : affine00191=(NestedInteger.clearedAll 3 raw00191 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/3200),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00191_transform
theorem leaf00191_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00191=true := by decide +kernel
#print axioms leaf00191_sign
theorem leaf00191_log : RationalLog.accepts (356370957/536870912) (-220001911/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00191_log
def leaf00191 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (128048886041/1000000000000) (356370957/536870912) (-220001911/1073741824) 1 8 ![60,0,4] ![(13/3200),0,(1/16)] ![(3/32000),1,(1/16)] affine00191
theorem leaf00191_checked : FastNestedCellData.accepts 1 2 4 leaf00191=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (128048886041/1000000000000) (356370957/536870912) (-220001911/1073741824) 1 8 ![60,0,4] ![(13/3200),0,(1/16)] ![(3/32000),1,(1/16)] 36907578589405101234537365504000000000000 27636045767666932043095380632399882747904 215824179515455844597989638144000000000000 raw00191 affine00191
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00191_raw leaf00191_rectangular
    leaf00191_transform leaf00191_sign leaf00191_log
#print axioms leaf00191_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
