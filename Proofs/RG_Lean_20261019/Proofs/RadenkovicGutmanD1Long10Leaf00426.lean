/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00426 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 7932329378462837939000836096000000000000 9432700796651115603088061991512602312704 456997479391467473338376388608000000000000))
theorem leaf00426_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 7932329378462837939000836096000000000000 9432700796651115603088061991512602312704 456997479391467473338376388608000000000000 raw00426=true := by decide +kernel
#print axioms leaf00426_raw
theorem leaf00426_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00426=true := by decide +kernel
#print axioms leaf00426_rectangular
def affine00426 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00426 (IntegerComputedClassCell.leftNumerator ![(3/8),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/8),0,0] ![(1/32),1,(1/2)]))
theorem leaf00426_transform : affine00426=(NestedInteger.clearedAll 3 raw00426 (IntegerComputedClassCell.leftNumerator ![(3/8),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/8),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf00426_transform
theorem leaf00426_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00426=true := by decide +kernel
#print axioms leaf00426_sign
theorem leaf00426_log : RationalLog.accepts (5004058083/4294967296) (164073397/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00426_log
def leaf00426 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (5160149247/250000000000) (5004058083/4294967296) (164073397/2147483648) 0 8 ![52,0,4] ![(3/8),0,0] ![(1/32),1,(1/2)] affine00426
theorem leaf00426_checked : FastNestedCellData.accepts 1 0 4 leaf00426=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (5160149247/250000000000) (5004058083/4294967296) (164073397/2147483648) 0 8 ![52,0,4] ![(3/8),0,0] ![(1/32),1,(1/2)] 7932329378462837939000836096000000000000 9432700796651115603088061991512602312704 456997479391467473338376388608000000000000 raw00426 affine00426
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00426_raw leaf00426_rectangular
    leaf00426_transform leaf00426_sign leaf00426_log
#print axioms leaf00426_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
