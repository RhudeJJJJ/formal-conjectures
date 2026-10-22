/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00048 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2344543503941360609184519815168000000000000 477502997350131055010756815516386459648 3756968284759703098151141376000000000000))
theorem leaf00048_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2344543503941360609184519815168000000000000 477502997350131055010756815516386459648 3756968284759703098151141376000000000000 raw00048=true := by decide +kernel
#print axioms leaf00048_raw
theorem leaf00048_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00048=true := by decide +kernel
#print axioms leaf00048_rectangular
def affine00048 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00048 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00048_transform : affine00048=(NestedInteger.clearedAll 3 raw00048 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00048_transform
theorem leaf00048_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00048=true := by decide +kernel
#print axioms leaf00048_sign
theorem leaf00048_log : RationalLog.accepts (776097/4294967296) (-18508468355/4294967296) 13 8=true := by decide +kernel
#print axioms leaf00048_log
def leaf00048 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (127097958023/1000000000000) (776097/4294967296) (-18508468355/4294967296) 13 8 ![52,0,4] ![(17/3200),0,0] ![(1/3200),1,(1/4)] affine00048
theorem leaf00048_checked : FastNestedCellData.accepts 1 0 4 leaf00048=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (127097958023/1000000000000) (776097/4294967296) (-18508468355/4294967296) 13 8 ![52,0,4] ![(17/3200),0,0] ![(1/3200),1,(1/4)] 2344543503941360609184519815168000000000000 477502997350131055010756815516386459648 3756968284759703098151141376000000000000 raw00048 affine00048
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00048_raw leaf00048_rectangular
    leaf00048_transform leaf00048_sign leaf00048_log
#print axioms leaf00048_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
