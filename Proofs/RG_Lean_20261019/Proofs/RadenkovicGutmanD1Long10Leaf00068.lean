/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00068 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 491897237539551534949821579264000000000000 461279899515673122649677764342458387267584 17298556697074144829258592157696000000000000))
theorem leaf00068_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 491897237539551534949821579264000000000000 461279899515673122649677764342458387267584 17298556697074144829258592157696000000000000 raw00068=true := by decide +kernel
#print axioms leaf00068_raw
theorem leaf00068_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00068=true := by decide +kernel
#print axioms leaf00068_rectangular
def affine00068 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00068 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00068_transform : affine00068=(NestedInteger.clearedAll 3 raw00068 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00068_transform
theorem leaf00068_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00068=true := by decide +kernel
#print axioms leaf00068_sign
theorem leaf00068_log : RationalLog.accepts (3923023519/4294967296) (-194521851/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00068_log
def leaf00068 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (26665802679/1000000000000) (3923023519/4294967296) (-194521851/4294967296) 1 8 ![52,0,4] ![(23/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00068
theorem leaf00068_checked : FastNestedCellData.accepts 1 0 4 leaf00068=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (26665802679/1000000000000) (3923023519/4294967296) (-194521851/4294967296) 1 8 ![52,0,4] ![(23/3200),0,(1/2)] ![(1/3200),1,(1/2)] 491897237539551534949821579264000000000000 461279899515673122649677764342458387267584 17298556697074144829258592157696000000000000 raw00068 affine00068
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00068_raw leaf00068_rectangular
    leaf00068_transform leaf00068_sign leaf00068_log
#print axioms leaf00068_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
