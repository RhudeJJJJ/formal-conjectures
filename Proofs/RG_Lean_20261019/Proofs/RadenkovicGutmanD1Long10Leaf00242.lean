/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00242 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 969582386438221830318114996224000000000000 707566046740673664796595489567371520114688 4487254843610019415098826686464000000000000))
theorem leaf00242_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 969582386438221830318114996224000000000000 707566046740673664796595489567371520114688 4487254843610019415098826686464000000000000 raw00242=true := by decide +kernel
#print axioms leaf00242_raw
theorem leaf00242_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00242=true := by decide +kernel
#print axioms leaf00242_rectangular
def affine00242 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00242 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00242_transform : affine00242=(NestedInteger.clearedAll 3 raw00242 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00242_transform
theorem leaf00242_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00242=true := by decide +kernel
#print axioms leaf00242_sign
theorem leaf00242_log : RationalLog.accepts (2707399131/4294967296) (-495484085/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00242_log
def leaf00242 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (157683499467/1000000000000) (2707399131/4294967296) (-495484085/2147483648) 1 8 ![52,0,4] ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)] affine00242
theorem leaf00242_checked : FastNestedCellData.accepts 1 0 4 leaf00242=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (157683499467/1000000000000) (2707399131/4294967296) (-495484085/2147483648) 1 8 ![52,0,4] ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)] 969582386438221830318114996224000000000000 707566046740673664796595489567371520114688 4487254843610019415098826686464000000000000 raw00242 affine00242
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00242_raw leaf00242_rectangular
    leaf00242_transform leaf00242_sign leaf00242_log
#print axioms leaf00242_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
