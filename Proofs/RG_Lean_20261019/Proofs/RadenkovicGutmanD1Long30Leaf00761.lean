/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00761 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12157828642790544313742971109376000000000000 3122086978030923078268791643783354084491264 4737058002026480535582093082624000000000000))
theorem leaf00761_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12157828642790544313742971109376000000000000 3122086978030923078268791643783354084491264 4737058002026480535582093082624000000000000 raw00761=true := by decide +kernel
#print axioms leaf00761_raw
theorem leaf00761_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00761=true := by decide +kernel
#print axioms leaf00761_rectangular
def affine00761 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00761 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00761_transform : affine00761=(NestedInteger.clearedAll 3 raw00761 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00761_transform
theorem leaf00761_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00761=true := by decide +kernel
#print axioms leaf00761_sign
theorem leaf00761_log : RationalLog.accepts (664786579/4294967296) (-4006631569/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00761_log
def leaf00761 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (659077211361/1000000000000) (664786579/4294967296) (-4006631569/4294967296) 3 8 ![60,0,4] ![(7/200),0,(1/16)] ![(3/3200),1,(1/16)] affine00761
theorem leaf00761_checked : FastNestedCellData.accepts 1 2 4 leaf00761=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (659077211361/1000000000000) (664786579/4294967296) (-4006631569/4294967296) 3 8 ![60,0,4] ![(7/200),0,(1/16)] ![(3/3200),1,(1/16)] 12157828642790544313742971109376000000000000 3122086978030923078268791643783354084491264 4737058002026480535582093082624000000000000 raw00761 affine00761
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00761_raw leaf00761_rectangular
    leaf00761_transform leaf00761_sign leaf00761_log
#print axioms leaf00761_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
