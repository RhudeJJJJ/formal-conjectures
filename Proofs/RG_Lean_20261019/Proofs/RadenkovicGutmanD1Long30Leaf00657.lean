/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00657 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6299942383071844684542045585408000000000000 3116276504733985003321863957235702607904768 9124711251361041428455238926336000000000000))
theorem leaf00657_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6299942383071844684542045585408000000000000 3116276504733985003321863957235702607904768 9124711251361041428455238926336000000000000 raw00657=true := by decide +kernel
#print axioms leaf00657_raw
theorem leaf00657_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00657=true := by decide +kernel
#print axioms leaf00657_rectangular
def affine00657 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00657 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00657_transform : affine00657=(NestedInteger.clearedAll 3 raw00657 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00657_transform
theorem leaf00657_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00657=true := by decide +kernel
#print axioms leaf00657_sign
theorem leaf00657_log : RationalLog.accepts (1583659957/4294967296) (-2142555983/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00657_log
def leaf00657 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (341520560913/1000000000000) (1583659957/4294967296) (-2142555983/4294967296) 2 8 ![60,0,4] ![(79/3200),0,(1/8)] ![(3/6400),1,(1/8)] affine00657
theorem leaf00657_checked : FastNestedCellData.accepts 1 2 4 leaf00657=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (341520560913/1000000000000) (1583659957/4294967296) (-2142555983/4294967296) 2 8 ![60,0,4] ![(79/3200),0,(1/8)] ![(3/6400),1,(1/8)] 6299942383071844684542045585408000000000000 3116276504733985003321863957235702607904768 9124711251361041428455238926336000000000000 raw00657 affine00657
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00657_raw leaf00657_rectangular
    leaf00657_transform leaf00657_sign leaf00657_log
#print axioms leaf00657_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
