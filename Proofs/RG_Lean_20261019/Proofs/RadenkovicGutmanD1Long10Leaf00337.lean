/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00337 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2280294024187683642102297657344000000000000 1306735078769738177765952695880732572123136 2642752131360675625370728267776000000000000))
theorem leaf00337_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2280294024187683642102297657344000000000000 1306735078769738177765952695880732572123136 2642752131360675625370728267776000000000000 raw00337=true := by decide +kernel
#print axioms leaf00337_raw
theorem leaf00337_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00337=true := by decide +kernel
#print axioms leaf00337_rectangular
def affine00337 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00337 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00337_transform : affine00337=(NestedInteger.clearedAll 3 raw00337 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00337_transform
theorem leaf00337_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00337=true := by decide +kernel
#print axioms leaf00337_sign
theorem leaf00337_log : RationalLog.accepts (1646919159/4294967296) (-2058443839/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00337_log
def leaf00337 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (247229973493/500000000000) (1646919159/4294967296) (-2058443839/4294967296) 2 8 ![52,0,4] ![(21/160),0,(1/4)] ![(1/160),1,(1/4)] affine00337
theorem leaf00337_checked : FastNestedCellData.accepts 1 0 4 leaf00337=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (247229973493/500000000000) (1646919159/4294967296) (-2058443839/4294967296) 2 8 ![52,0,4] ![(21/160),0,(1/4)] ![(1/160),1,(1/4)] 2280294024187683642102297657344000000000000 1306735078769738177765952695880732572123136 2642752131360675625370728267776000000000000 raw00337 affine00337
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00337_raw leaf00337_rectangular
    leaf00337_transform leaf00337_sign leaf00337_log
#print axioms leaf00337_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
