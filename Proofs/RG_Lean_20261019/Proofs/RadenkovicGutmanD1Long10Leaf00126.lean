/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00126 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3037634970376368839248345825280000000000 10819177657740511369365447118384267264 32850984941684318232012390400000000000))
theorem leaf00126_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3037634970376368839248345825280000000000 10819177657740511369365447118384267264 32850984941684318232012390400000000000 raw00126=true := by decide +kernel
#print axioms leaf00126_raw
theorem leaf00126_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00126=true := by decide +kernel
#print axioms leaf00126_rectangular
def affine00126 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00126 (IntegerComputedClassCell.leftNumerator ![(3/200),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/200),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00126_transform : affine00126=(NestedInteger.clearedAll 3 raw00126 (IntegerComputedClassCell.leftNumerator ![(3/200),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/200),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00126_transform
theorem leaf00126_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00126=true := by decide +kernel
#print axioms leaf00126_sign
theorem leaf00126_log : RationalLog.accepts (5753765/2147483648) (-12717822859/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00126_log
def leaf00126 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (32934104341/100000000000) (5753765/2147483648) (-12717822859/4294967296) 9 8 ![52,0,4] ![(3/200),0,0] ![(1/1600),1,(1/4)] affine00126
theorem leaf00126_checked : FastNestedCellData.accepts 1 0 4 leaf00126=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (32934104341/100000000000) (5753765/2147483648) (-12717822859/4294967296) 9 8 ![52,0,4] ![(3/200),0,0] ![(1/1600),1,(1/4)] 3037634970376368839248345825280000000000 10819177657740511369365447118384267264 32850984941684318232012390400000000000 raw00126 affine00126
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00126_raw leaf00126_rectangular
    leaf00126_transform leaf00126_sign leaf00126_log
#print axioms leaf00126_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
