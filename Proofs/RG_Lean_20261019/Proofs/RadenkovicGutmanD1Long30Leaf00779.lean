/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00779 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2433600291465959420612050944000000000000 1843427453196460936031640786040849956864 13645723532189593363602735104000000000000))
theorem leaf00779_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2433600291465959420612050944000000000000 1843427453196460936031640786040849956864 13645723532189593363602735104000000000000 raw00779=true := by decide +kernel
#print axioms leaf00779_raw
theorem leaf00779_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00779=true := by decide +kernel
#print axioms leaf00779_rectangular
def affine00779 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00779 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00779_transform : affine00779=(NestedInteger.clearedAll 3 raw00779 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00779_transform
theorem leaf00779_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00779=true := by decide +kernel
#print axioms leaf00779_sign
theorem leaf00779_log : RationalLog.accepts (716548559/1073741824) (-54285549/268435456) 1 8=true := by decide +kernel
#print axioms leaf00779_log
def leaf00779 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16886494227/125000000000) (716548559/1073741824) (-54285549/268435456) 1 8 ![60,0,4] ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00779
theorem leaf00779_checked : FastNestedCellData.accepts 1 2 4 leaf00779=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16886494227/125000000000) (716548559/1073741824) (-54285549/268435456) 1 8 ![60,0,4] ![(121/3200),0,(1/2)] ![(3/3200),1,(1/2)] 2433600291465959420612050944000000000000 1843427453196460936031640786040849956864 13645723532189593363602735104000000000000 raw00779 affine00779
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00779_raw leaf00779_rectangular
    leaf00779_transform leaf00779_sign leaf00779_log
#print axioms leaf00779_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
