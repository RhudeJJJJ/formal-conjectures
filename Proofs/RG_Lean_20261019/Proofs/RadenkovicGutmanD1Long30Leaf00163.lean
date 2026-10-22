/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00163 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 121578812081989582707490816000000000000 114135559792013668752095543143948091392 4227881945436294015512215552000000000000))
theorem leaf00163_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 121578812081989582707490816000000000000 114135559792013668752095543143948091392 4227881945436294015512215552000000000000 raw00163=true := by decide +kernel
#print axioms leaf00163_raw
theorem leaf00163_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00163=true := by decide +kernel
#print axioms leaf00163_rectangular
def affine00163 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00163 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00163_transform : affine00163=(NestedInteger.clearedAll 3 raw00163 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00163_transform
theorem leaf00163_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00163=true := by decide +kernel
#print axioms leaf00163_sign
theorem leaf00163_log : RationalLog.accepts (3926035487/4294967296) (-48218429/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00163_log
def leaf00163 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (421811239/15625000000) (3926035487/4294967296) (-48218429/1073741824) 1 8 ![60,0,4] ![(7/2000),0,(1/4)] ![(3/32000),1,(1/4)] affine00163
theorem leaf00163_checked : FastNestedCellData.accepts 1 2 4 leaf00163=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (421811239/15625000000) (3926035487/4294967296) (-48218429/1073741824) 1 8 ![60,0,4] ![(7/2000),0,(1/4)] ![(3/32000),1,(1/4)] 121578812081989582707490816000000000000 114135559792013668752095543143948091392 4227881945436294015512215552000000000000 raw00163 affine00163
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00163_raw leaf00163_rectangular
    leaf00163_transform leaf00163_sign leaf00163_log
#print axioms leaf00163_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
