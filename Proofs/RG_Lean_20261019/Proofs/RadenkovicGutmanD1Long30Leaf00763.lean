/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00763 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 226501176062053373855416293785600000000000 138547249165987634298377500928591555198976 564179332733631897260122963968000000000000))
theorem leaf00763_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 226501176062053373855416293785600000000000 138547249165987634298377500928591555198976 564179332733631897260122963968000000000000 raw00763=true := by decide +kernel
#print axioms leaf00763_raw
theorem leaf00763_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00763=true := by decide +kernel
#print axioms leaf00763_rectangular
def affine00763 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00763 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00763_transform : affine00763=(NestedInteger.clearedAll 3 raw00763 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00763_transform
theorem leaf00763_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00763=true := by decide +kernel
#print axioms leaf00763_sign
theorem leaf00763_log : RationalLog.accepts (1054600815/2147483648) (-1527149653/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00763_log
def leaf00763 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (245573067157/1000000000000) (1054600815/2147483648) (-1527149653/4294967296) 2 8 ![60,0,4] ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)] affine00763
theorem leaf00763_checked : FastNestedCellData.accepts 1 2 4 leaf00763=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (245573067157/1000000000000) (1054600815/2147483648) (-1527149653/4294967296) 2 8 ![60,0,4] ![(7/200),0,(1/4)] ![(3/3200),1,(1/4)] 226501176062053373855416293785600000000000 138547249165987634298377500928591555198976 564179332733631897260122963968000000000000 raw00763 affine00763
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00763_raw leaf00763_rectangular
    leaf00763_transform leaf00763_sign leaf00763_log
#print axioms leaf00763_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
