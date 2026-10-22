/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00325 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 8808855349888804381678284832768000000000000 4691083175089634277038286070292426593927168 9823661227500534002496009404416000000000000))
theorem leaf00325_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 8808855349888804381678284832768000000000000 4691083175089634277038286070292426593927168 9823661227500534002496009404416000000000000 raw00325=true := by decide +kernel
#print axioms leaf00325_raw
theorem leaf00325_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00325=true := by decide +kernel
#print axioms leaf00325_rectangular
def affine00325 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00325 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00325_transform : affine00325=(NestedInteger.clearedAll 3 raw00325 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00325_transform
theorem leaf00325_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00325=true := by decide +kernel
#print axioms leaf00325_sign
theorem leaf00325_log : RationalLog.accepts (1548023327/4294967296) (-547858045/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00325_log
def leaf00325 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (477529005373/1000000000000) (1548023327/4294967296) (-547858045/1073741824) 2 8 ![52,0,4] ![(17/160),0,(1/4)] ![(1/160),1,(1/4)] affine00325
theorem leaf00325_checked : FastNestedCellData.accepts 1 0 4 leaf00325=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (477529005373/1000000000000) (1548023327/4294967296) (-547858045/1073741824) 2 8 ![52,0,4] ![(17/160),0,(1/4)] ![(1/160),1,(1/4)] 8808855349888804381678284832768000000000000 4691083175089634277038286070292426593927168 9823661227500534002496009404416000000000000 raw00325 affine00325
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00325_raw leaf00325_rectangular
    leaf00325_transform leaf00325_sign leaf00325_log
#print axioms leaf00325_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
