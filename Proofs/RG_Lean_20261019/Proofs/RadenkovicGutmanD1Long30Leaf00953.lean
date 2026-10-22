/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00953 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2049228090215531016209525899264000000000000 1109226381553993874093832058825475331457024 2496258869136102554939649163264000000000000))
theorem leaf00953_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2049228090215531016209525899264000000000000 1109226381553993874093832058825475331457024 2496258869136102554939649163264000000000000 raw00953=true := by decide +kernel
#print axioms leaf00953_raw
theorem leaf00953_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00953=true := by decide +kernel
#print axioms leaf00953_rectangular
def affine00953 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00953 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00953_transform : affine00953=(NestedInteger.clearedAll 3 raw00953 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00953_transform
theorem leaf00953_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00953=true := by decide +kernel
#print axioms leaf00953_sign
theorem leaf00953_log : RationalLog.accepts (1609591421/4294967296) (-2107677039/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00953_log
def leaf00953 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (222177754733/500000000000) (1609591421/4294967296) (-2107677039/4294967296) 2 8 ![60,0,4] ![(31/320),0,(1/4)] ![(1/320),1,(1/4)] affine00953
theorem leaf00953_checked : FastNestedCellData.accepts 1 2 4 leaf00953=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (222177754733/500000000000) (1609591421/4294967296) (-2107677039/4294967296) 2 8 ![60,0,4] ![(31/320),0,(1/4)] ![(1/320),1,(1/4)] 2049228090215531016209525899264000000000000 1109226381553993874093832058825475331457024 2496258869136102554939649163264000000000000 raw00953 affine00953
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00953_raw leaf00953_rectangular
    leaf00953_transform leaf00953_sign leaf00953_log
#print axioms leaf00953_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
