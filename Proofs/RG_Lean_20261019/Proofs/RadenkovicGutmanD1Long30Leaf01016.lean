/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01016 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2567862050602442058668965888000000000000 1651795809535680384402678762908854255616 2896972985979437093614518272000000000000))
theorem leaf01016_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2567862050602442058668965888000000000000 1651795809535680384402678762908854255616 2896972985979437093614518272000000000000 raw01016=true := by decide +kernel
#print axioms leaf01016_raw
theorem leaf01016_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01016=true := by decide +kernel
#print axioms leaf01016_rectangular
def affine01016 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01016 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/16)] ![(1/80),1,(1/16)]))
theorem leaf01016_transform : affine01016=(NestedInteger.clearedAll 3 raw01016 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/16)] ![(1/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01016_transform
theorem leaf01016_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01016=true := by decide +kernel
#print axioms leaf01016_sign
theorem leaf01016_log : RationalLog.accepts (879761837/2147483648) (-958208107/2147483648) 2 8=true := by decide +kernel
#print axioms leaf01016_log
def leaf01016 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17818122329/31250000000) (879761837/2147483648) (-958208107/2147483648) 2 8 ![60,0,4] ![(7/40),0,(1/16)] ![(1/80),1,(1/16)] affine01016
theorem leaf01016_checked : FastNestedCellData.accepts 1 2 4 leaf01016=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17818122329/31250000000) (879761837/2147483648) (-958208107/2147483648) 2 8 ![60,0,4] ![(7/40),0,(1/16)] ![(1/80),1,(1/16)] 2567862050602442058668965888000000000000 1651795809535680384402678762908854255616 2896972985979437093614518272000000000000 raw01016 affine01016
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01016_raw leaf01016_rectangular
    leaf01016_transform leaf01016_sign leaf01016_log
#print axioms leaf01016_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
