/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00455 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 827593915346998109999583985664000000000000 3837365245904982247931370781354242342912 5345835476786704821107294208000000000000))
theorem leaf00455_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 827593915346998109999583985664000000000000 3837365245904982247931370781354242342912 5345835476786704821107294208000000000000 raw00455=true := by decide +kernel
#print axioms leaf00455_raw
theorem leaf00455_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00455=true := by decide +kernel
#print axioms leaf00455_rectangular
def affine00455 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00455 (IntegerComputedClassCell.leftNumerator ![(3/256),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/256),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00455_transform : affine00455=(NestedInteger.clearedAll 3 raw00455 (IntegerComputedClassCell.leftNumerator ![(3/256),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/256),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00455_transform
theorem leaf00455_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00455=true := by decide +kernel
#print axioms leaf00455_sign
theorem leaf00455_log : RationalLog.accepts (11593037/4294967296) (-6350962459/2147483648) 9 8=true := by decide +kernel
#print axioms leaf00455_log
def leaf00455 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (179455824191/250000000000) (11593037/4294967296) (-6350962459/2147483648) 9 8 ![60,0,4] ![(3/256),0,0] ![(1/6400),1,(1/16)] affine00455
theorem leaf00455_checked : FastNestedCellData.accepts 1 2 4 leaf00455=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (179455824191/250000000000) (11593037/4294967296) (-6350962459/2147483648) 9 8 ![60,0,4] ![(3/256),0,0] ![(1/6400),1,(1/16)] 827593915346998109999583985664000000000000 3837365245904982247931370781354242342912 5345835476786704821107294208000000000000 raw00455 affine00455
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00455_raw leaf00455_rectangular
    leaf00455_transform leaf00455_sign leaf00455_log
#print axioms leaf00455_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
