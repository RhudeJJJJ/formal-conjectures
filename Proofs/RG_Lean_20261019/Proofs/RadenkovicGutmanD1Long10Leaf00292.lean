/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00292 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 18907569105866254769686629580800000000000 9653660692671721357519177830568172716032 23545941730406570858204731801600000000000))
theorem leaf00292_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 18907569105866254769686629580800000000000 9653660692671721357519177830568172716032 23545941730406570858204731801600000000000 raw00292=true := by decide +kernel
#print axioms leaf00292_raw
theorem leaf00292_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00292=true := by decide +kernel
#print axioms leaf00292_rectangular
def affine00292 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00292 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00292_transform : affine00292=(NestedInteger.clearedAll 3 raw00292 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00292_transform
theorem leaf00292_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00292=true := by decide +kernel
#print axioms leaf00292_sign
theorem leaf00292_log : RationalLog.accepts (1555247017/4294967296) (-2181434479/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00292_log
def leaf00292 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (20499627501/50000000000) (1555247017/4294967296) (-2181434479/4294967296) 2 8 ![52,0,4] ![(23/320),0,(1/4)] ![(1/320),1,(1/4)] affine00292
theorem leaf00292_checked : FastNestedCellData.accepts 1 0 4 leaf00292=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (20499627501/50000000000) (1555247017/4294967296) (-2181434479/4294967296) 2 8 ![52,0,4] ![(23/320),0,(1/4)] ![(1/320),1,(1/4)] 18907569105866254769686629580800000000000 9653660692671721357519177830568172716032 23545941730406570858204731801600000000000 raw00292 affine00292
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00292_raw leaf00292_rectangular
    leaf00292_transform leaf00292_sign leaf00292_log
#print axioms leaf00292_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
