/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00113 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 12722965123632812662133358592000000000000 11451785636305981611700336150724648894464 259432644001367230635676008448000000000000))
theorem leaf00113_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 12722965123632812662133358592000000000000 11451785636305981611700336150724648894464 259432644001367230635676008448000000000000 raw00113=true := by decide +kernel
#print axioms leaf00113_raw
theorem leaf00113_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00113=true := by decide +kernel
#print axioms leaf00113_rectangular
def affine00113 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00113 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00113_transform : affine00113=(NestedInteger.clearedAll 3 raw00113 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00113_transform
theorem leaf00113_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00113=true := by decide +kernel
#print axioms leaf00113_sign
theorem leaf00113_log : RationalLog.accepts (3702416849/4294967296) (-318811447/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00113_log
def leaf00113 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (5517706571/125000000000) (3702416849/4294967296) (-318811447/4294967296) 1 8 ![52,0,4] ![(19/1600),0,(1/2)] ![(1/1600),1,(1/2)] affine00113
theorem leaf00113_checked : FastNestedCellData.accepts 1 0 4 leaf00113=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (5517706571/125000000000) (3702416849/4294967296) (-318811447/4294967296) 1 8 ![52,0,4] ![(19/1600),0,(1/2)] ![(1/1600),1,(1/2)] 12722965123632812662133358592000000000000 11451785636305981611700336150724648894464 259432644001367230635676008448000000000000 raw00113 affine00113
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00113_raw leaf00113_rectangular
    leaf00113_transform leaf00113_sign leaf00113_log
#print axioms leaf00113_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
