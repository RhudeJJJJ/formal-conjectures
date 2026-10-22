/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00039 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1865630526640644478524719104000000000000 202382532601995058124016581028610048 1954191648126273593540608000000000000))
theorem leaf00039_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1865630526640644478524719104000000000000 202382532601995058124016581028610048 1954191648126273593540608000000000000 raw00039=true := by decide +kernel
#print axioms leaf00039_raw
theorem leaf00039_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00039=true := by decide +kernel
#print axioms leaf00039_rectangular
def affine00039 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00039 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/4000),0,0] ![(3/8000),1,(1/4)]))
theorem leaf00039_transform : affine00039=(NestedInteger.clearedAll 3 raw00039 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/4000),0,0] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00039_transform
theorem leaf00039_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00039=true := by decide +kernel
#print axioms leaf00039_sign
theorem leaf00039_log : RationalLog.accepts (26387/268435456) (-19815893641/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00039_log
def leaf00039 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (51781649153/500000000000) (26387/268435456) (-19815893641/4294967296) 14 8 ![52,0,4] ![(17/4000),0,0] ![(3/8000),1,(1/4)] affine00039
theorem leaf00039_checked : FastNestedCellData.accepts 1 0 4 leaf00039=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (51781649153/500000000000) (26387/268435456) (-19815893641/4294967296) 14 8 ![52,0,4] ![(17/4000),0,0] ![(3/8000),1,(1/4)] 1865630526640644478524719104000000000000 202382532601995058124016581028610048 1954191648126273593540608000000000000 raw00039 affine00039
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00039_raw leaf00039_rectangular
    leaf00039_transform leaf00039_sign leaf00039_log
#print axioms leaf00039_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
