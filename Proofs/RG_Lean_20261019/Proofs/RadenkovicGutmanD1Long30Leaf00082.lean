/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00082 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9175568176384561758494261248000000000000 8509773177896847862380084303553938587648 267315884627584986273435090944000000000000))
theorem leaf00082_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9175568176384561758494261248000000000000 8509773177896847862380084303553938587648 267315884627584986273435090944000000000000 raw00082=true := by decide +kernel
#print axioms leaf00082_raw
theorem leaf00082_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00082=true := by decide +kernel
#print axioms leaf00082_rectangular
def affine00082 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00082 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00082_transform : affine00082=(NestedInteger.clearedAll 3 raw00082 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00082_transform
theorem leaf00082_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00082=true := by decide +kernel
#print axioms leaf00082_sign
theorem leaf00082_log : RationalLog.accepts (965105947/1073741824) (-114532809/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00082_log
def leaf00082 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15917073521/500000000000) (965105947/1073741824) (-114532809/2147483648) 1 8 ![60,0,4] ![(1/500),0,(1/8)] ![(3/32000),1,(1/8)] affine00082
theorem leaf00082_checked : FastNestedCellData.accepts 1 2 4 leaf00082=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15917073521/500000000000) (965105947/1073741824) (-114532809/2147483648) 1 8 ![60,0,4] ![(1/500),0,(1/8)] ![(3/32000),1,(1/8)] 9175568176384561758494261248000000000000 8509773177896847862380084303553938587648 267315884627584986273435090944000000000000 raw00082 affine00082
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00082_raw leaf00082_rectangular
    leaf00082_transform leaf00082_sign leaf00082_log
#print axioms leaf00082_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
