/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00695 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 251117087472807184688903880704000000000000 7535835088068681400412918600408380735488 8649576991794754656946618368000000000000))
theorem leaf00695_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 251117087472807184688903880704000000000000 7535835088068681400412918600408380735488 8649576991794754656946618368000000000000 raw00695=true := by decide +kernel
#print axioms leaf00695_raw
theorem leaf00695_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00695=true := by decide +kernel
#print axioms leaf00695_rectangular
def affine00695 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00695 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(91/3200),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00695_transform : affine00695=(NestedInteger.clearedAll 3 raw00695 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(91/3200),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00695_transform
theorem leaf00695_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00695=true := by decide +kernel
#print axioms leaf00695_sign
theorem leaf00695_log : RationalLog.accepts (34439441/2147483648) (-1109403391/536870912) 6 8=true := by decide +kernel
#print axioms leaf00695_log
def leaf00695 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (217809353429/250000000000) (34439441/2147483648) (-1109403391/536870912) 6 8 ![60,0,4] ![(91/3200),0,0] ![(3/6400),1,(1/16)] affine00695
theorem leaf00695_checked : FastNestedCellData.accepts 1 2 4 leaf00695=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (217809353429/250000000000) (34439441/2147483648) (-1109403391/536870912) 6 8 ![60,0,4] ![(91/3200),0,0] ![(3/6400),1,(1/16)] 251117087472807184688903880704000000000000 7535835088068681400412918600408380735488 8649576991794754656946618368000000000000 raw00695 affine00695
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00695_raw leaf00695_rectangular
    leaf00695_transform leaf00695_sign leaf00695_log
#print axioms leaf00695_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
