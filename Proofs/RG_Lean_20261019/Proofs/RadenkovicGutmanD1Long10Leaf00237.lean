/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00237 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2346766860829194394461769459302400000000000 112363528344172710680456287018770556256256 176646541689411070607971319808000000000000))
theorem leaf00237_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2346766860829194394461769459302400000000000 112363528344172710680456287018770556256256 176646541689411070607971319808000000000000 raw00237=true := by decide +kernel
#print axioms leaf00237_raw
theorem leaf00237_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00237=true := by decide +kernel
#print axioms leaf00237_rectangular
def affine00237 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00237 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/1600),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00237_transform : affine00237=(NestedInteger.clearedAll 3 raw00237 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/1600),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00237_transform
theorem leaf00237_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00237=true := by decide +kernel
#print axioms leaf00237_sign
theorem leaf00237_log : RationalLog.accepts (125691945/4294967296) (-947943651/536870912) 6 8=true := by decide +kernel
#print axioms leaf00237_log
def leaf00237 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (636092432207/1000000000000) (125691945/4294967296) (-947943651/536870912) 6 8 ![52,0,4] ![(71/1600),0,0] ![(3/3200),1,(1/4)] affine00237
theorem leaf00237_checked : FastNestedCellData.accepts 1 0 4 leaf00237=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (636092432207/1000000000000) (125691945/4294967296) (-947943651/536870912) 6 8 ![52,0,4] ![(71/1600),0,0] ![(3/3200),1,(1/4)] 2346766860829194394461769459302400000000000 112363528344172710680456287018770556256256 176646541689411070607971319808000000000000 raw00237 affine00237
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00237_raw leaf00237_rectangular
    leaf00237_transform leaf00237_sign leaf00237_log
#print axioms leaf00237_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
