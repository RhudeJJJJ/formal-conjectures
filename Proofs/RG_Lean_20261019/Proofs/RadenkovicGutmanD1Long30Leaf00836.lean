/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00836 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2629938290785081823888710146457600000000000 665335193770053123983403140092632338792448 933350268005287834947195764736000000000000))
theorem leaf00836_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2629938290785081823888710146457600000000000 665335193770053123983403140092632338792448 933350268005287834947195764736000000000000 raw00836=true := by decide +kernel
#print axioms leaf00836_raw
theorem leaf00836_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00836=true := by decide +kernel
#print axioms leaf00836_rectangular
def affine00836 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00836 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(157/3200),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00836_transform : affine00836=(NestedInteger.clearedAll 3 raw00836 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(157/3200),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00836_transform
theorem leaf00836_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00836=true := by decide +kernel
#print axioms leaf00836_sign
theorem leaf00836_log : RationalLog.accepts (634360935/4294967296) (-4107236807/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00836_log
def leaf00836 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (712846202093/1000000000000) (634360935/4294967296) (-4107236807/4294967296) 3 8 ![60,0,4] ![(157/3200),0,(1/16)] ![(3/3200),1,(1/16)] affine00836
theorem leaf00836_checked : FastNestedCellData.accepts 1 2 4 leaf00836=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (712846202093/1000000000000) (634360935/4294967296) (-4107236807/4294967296) 3 8 ![60,0,4] ![(157/3200),0,(1/16)] ![(3/3200),1,(1/16)] 2629938290785081823888710146457600000000000 665335193770053123983403140092632338792448 933350268005287834947195764736000000000000 raw00836 affine00836
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00836_raw leaf00836_rectangular
    leaf00836_transform leaf00836_sign leaf00836_log
#print axioms leaf00836_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
