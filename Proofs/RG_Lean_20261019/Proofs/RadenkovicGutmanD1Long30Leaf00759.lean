/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00759 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 566612034134448630366461755392000000000000 437929264942900226469090794957796934680576 3564329993948093463119645376512000000000000))
theorem leaf00759_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 566612034134448630366461755392000000000000 437929264942900226469090794957796934680576 3564329993948093463119645376512000000000000 raw00759=true := by decide +kernel
#print axioms leaf00759_raw
theorem leaf00759_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00759=true := by decide +kernel
#print axioms leaf00759_rectangular
def affine00759 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00759 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00759_transform : affine00759=(NestedInteger.clearedAll 3 raw00759 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00759_transform
theorem leaf00759_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00759=true := by decide +kernel
#print axioms leaf00759_sign
theorem leaf00759_log : RationalLog.accepts (1478157553/2147483648) (-802085919/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00759_log
def leaf00759 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (122864399673/1000000000000) (1478157553/2147483648) (-802085919/4294967296) 1 8 ![60,0,4] ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00759
theorem leaf00759_checked : FastNestedCellData.accepts 1 2 4 leaf00759=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (122864399673/1000000000000) (1478157553/2147483648) (-802085919/4294967296) 1 8 ![60,0,4] ![(109/3200),0,(1/2)] ![(3/3200),1,(1/2)] 566612034134448630366461755392000000000000 437929264942900226469090794957796934680576 3564329993948093463119645376512000000000000 raw00759 affine00759
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00759_raw leaf00759_rectangular
    leaf00759_transform leaf00759_sign leaf00759_log
#print axioms leaf00759_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
