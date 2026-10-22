/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00257 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 39958550806472601686455091200000000000 28297602585613064958245556567914053632 159466584608221214306992128000000000000))
theorem leaf00257_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 39958550806472601686455091200000000000 28297602585613064958245556567914053632 159466584608221214306992128000000000000 raw00257=true := by decide +kernel
#print axioms leaf00257_raw
theorem leaf00257_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00257=true := by decide +kernel
#print axioms leaf00257_rectangular
def affine00257 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00257 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00257_transform : affine00257=(NestedInteger.clearedAll 3 raw00257 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00257_transform
theorem leaf00257_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00257=true := by decide +kernel
#print axioms leaf00257_sign
theorem leaf00257_log : RationalLog.accepts (2583192115/4294967296) (-1091819491/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00257_log
def leaf00257 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1386340723/7812500000) (2583192115/4294967296) (-1091819491/4294967296) 1 8 ![52,0,4] ![(33/640),0,(1/2)] ![(1/640),1,(1/2)] affine00257
theorem leaf00257_checked : FastNestedCellData.accepts 1 0 4 leaf00257=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1386340723/7812500000) (2583192115/4294967296) (-1091819491/4294967296) 1 8 ![52,0,4] ![(33/640),0,(1/2)] ![(1/640),1,(1/2)] 39958550806472601686455091200000000000 28297602585613064958245556567914053632 159466584608221214306992128000000000000 raw00257 affine00257
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00257_raw leaf00257_rectangular
    leaf00257_transform leaf00257_sign leaf00257_log
#print axioms leaf00257_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
