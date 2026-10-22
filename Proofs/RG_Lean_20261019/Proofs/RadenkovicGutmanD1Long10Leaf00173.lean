/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00173 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1249517854887195836645847859200000000000 1028764825413733833610390881690779123712 11865427590365243596228001792000000000000))
theorem leaf00173_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1249517854887195836645847859200000000000 1028764825413733833610390881690779123712 11865427590365243596228001792000000000000 raw00173=true := by decide +kernel
#print axioms leaf00173_raw
theorem leaf00173_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00173=true := by decide +kernel
#print axioms leaf00173_rectangular
def affine00173 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00173 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00173_transform : affine00173=(NestedInteger.clearedAll 3 raw00173 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00173_transform
theorem leaf00173_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00173=true := by decide +kernel
#print axioms leaf00173_sign
theorem leaf00173_log : RationalLog.accepts (203377435/268435456) (-74503449/536870912) 1 8=true := by decide +kernel
#print axioms leaf00173_log
def leaf00173 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (86702718261/1000000000000) (203377435/268435456) (-74503449/536870912) 1 8 ![52,0,4] ![(19/800),0,(1/2)] ![(3/3200),1,(1/2)] affine00173
theorem leaf00173_checked : FastNestedCellData.accepts 1 0 4 leaf00173=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (86702718261/1000000000000) (203377435/268435456) (-74503449/536870912) 1 8 ![52,0,4] ![(19/800),0,(1/2)] ![(3/3200),1,(1/2)] 1249517854887195836645847859200000000000 1028764825413733833610390881690779123712 11865427590365243596228001792000000000000 raw00173 affine00173
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00173_raw leaf00173_rectangular
    leaf00173_transform leaf00173_sign leaf00173_log
#print axioms leaf00173_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
