/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00255 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 12281218126813911367463246757888000000000000 808962916598490545789476440827503174483968 1215085648143713111636942258176000000000000))
theorem leaf00255_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 12281218126813911367463246757888000000000000 808962916598490545789476440827503174483968 1215085648143713111636942258176000000000000 raw00255=true := by decide +kernel
#print axioms leaf00255_raw
theorem leaf00255_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00255=true := by decide +kernel
#print axioms leaf00255_rectangular
def affine00255 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00255 (IntegerComputedClassCell.leftNumerator ![(33/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/640),0,0] ![(1/640),1,(1/4)]))
theorem leaf00255_transform : affine00255=(NestedInteger.clearedAll 3 raw00255 (IntegerComputedClassCell.leftNumerator ![(33/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/640),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00255_transform
theorem leaf00255_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00255=true := by decide +kernel
#print axioms leaf00255_sign
theorem leaf00255_log : RationalLog.accepts (169837267/4294967296) (-1734285555/1073741824) 5 8=true := by decide +kernel
#print axioms leaf00255_log
def leaf00255 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (665766168693/1000000000000) (169837267/4294967296) (-1734285555/1073741824) 5 8 ![52,0,4] ![(33/640),0,0] ![(1/640),1,(1/4)] affine00255
theorem leaf00255_checked : FastNestedCellData.accepts 1 0 4 leaf00255=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (665766168693/1000000000000) (169837267/4294967296) (-1734285555/1073741824) 5 8 ![52,0,4] ![(33/640),0,0] ![(1/640),1,(1/4)] 12281218126813911367463246757888000000000000 808962916598490545789476440827503174483968 1215085648143713111636942258176000000000000 raw00255 affine00255
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00255_raw leaf00255_rectangular
    leaf00255_transform leaf00255_sign leaf00255_log
#print axioms leaf00255_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
