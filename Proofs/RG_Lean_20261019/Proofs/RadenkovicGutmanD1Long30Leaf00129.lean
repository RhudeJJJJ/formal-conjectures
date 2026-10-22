/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00129 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1922178767388215659724800000000 1873715211074908631661925105664 175602046377013219111731200000000))
theorem leaf00129_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1922178767388215659724800000000 1873715211074908631661925105664 175602046377013219111731200000000 raw00129=true := by decide +kernel
#print axioms leaf00129_raw
theorem leaf00129_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00129=true := by decide +kernel
#print axioms leaf00129_rectangular
def affine00129 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00129 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(91/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00129_transform : affine00129=(NestedInteger.clearedAll 3 raw00129 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(91/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00129_transform
theorem leaf00129_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00129=true := by decide +kernel
#print axioms leaf00129_sign
theorem leaf00129_log : RationalLog.accepts (8090777/8388608) (-9703899/536870912) 1 8=true := by decide +kernel
#print axioms leaf00129_log
def leaf00129 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17072377/1600000000) (8090777/8388608) (-9703899/536870912) 1 8 ![60,0,4] ![(91/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00129
theorem leaf00129_checked : FastNestedCellData.accepts 1 2 4 leaf00129=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17072377/1600000000) (8090777/8388608) (-9703899/536870912) 1 8 ![60,0,4] ![(91/32000),0,(1/2)] ![(3/32000),1,(1/2)] 1922178767388215659724800000000 1873715211074908631661925105664 175602046377013219111731200000000 raw00129 affine00129
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00129_raw leaf00129_rectangular
    leaf00129_transform leaf00129_sign leaf00129_log
#print axioms leaf00129_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
