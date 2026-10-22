/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00408 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 475388991887388080753946394624000000000000 399478223003117490078415561115288853282816 5167047525649895328534335848448000000000000))
theorem leaf00408_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 475388991887388080753946394624000000000000 399478223003117490078415561115288853282816 5167047525649895328534335848448000000000000 raw00408=true := by decide +kernel
#print axioms leaf00408_raw
theorem leaf00408_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00408=true := by decide +kernel
#print axioms leaf00408_rectangular
def affine00408 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00408 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/1280),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00408_transform : affine00408=(NestedInteger.clearedAll 3 raw00408 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/1280),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00408_transform
theorem leaf00408_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00408=true := by decide +kernel
#print axioms leaf00408_sign
theorem leaf00408_log : RationalLog.accepts (3350133267/4294967296) (-533529065/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00408_log
def leaf00408 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (77312666667/1000000000000) (3350133267/4294967296) (-533529065/4294967296) 1 8 ![60,0,4] ![(13/1280),0,(1/4)] ![(1/6400),1,(1/4)] affine00408
theorem leaf00408_checked : FastNestedCellData.accepts 1 2 4 leaf00408=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (77312666667/1000000000000) (3350133267/4294967296) (-533529065/4294967296) 1 8 ![60,0,4] ![(13/1280),0,(1/4)] ![(1/6400),1,(1/4)] 475388991887388080753946394624000000000000 399478223003117490078415561115288853282816 5167047525649895328534335848448000000000000 raw00408 affine00408
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00408_raw leaf00408_rectangular
    leaf00408_transform leaf00408_sign leaf00408_log
#print axioms leaf00408_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
