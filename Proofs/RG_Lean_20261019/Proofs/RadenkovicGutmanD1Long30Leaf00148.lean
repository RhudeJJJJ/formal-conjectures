/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00148 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 458570934902500617567378341888000000000000 432570149800730087455132845436294989348864 17400821203369201848366554677248000000000000))
theorem leaf00148_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 458570934902500617567378341888000000000000 432570149800730087455132845436294989348864 17400821203369201848366554677248000000000000 raw00148=true := by decide +kernel
#print axioms leaf00148_raw
theorem leaf00148_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00148=true := by decide +kernel
#print axioms leaf00148_rectangular
def affine00148 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00148 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(103/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00148_transform : affine00148=(NestedInteger.clearedAll 3 raw00148 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(103/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00148_transform
theorem leaf00148_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00148=true := by decide +kernel
#print axioms leaf00148_sign
theorem leaf00148_log : RationalLog.accepts (3953171791/4294967296) (-178081619/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00148_log
def leaf00148 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (24859180193/1000000000000) (3953171791/4294967296) (-178081619/4294967296) 1 8 ![60,0,4] ![(103/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00148
theorem leaf00148_checked : FastNestedCellData.accepts 1 2 4 leaf00148=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (24859180193/1000000000000) (3953171791/4294967296) (-178081619/4294967296) 1 8 ![60,0,4] ![(103/32000),0,(1/4)] ![(3/32000),1,(1/4)] 458570934902500617567378341888000000000000 432570149800730087455132845436294989348864 17400821203369201848366554677248000000000000 raw00148 affine00148
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00148_raw leaf00148_rectangular
    leaf00148_transform leaf00148_sign leaf00148_log
#print axioms leaf00148_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
