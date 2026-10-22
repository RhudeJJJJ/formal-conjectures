/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00193 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 144189752093574699110761496576000000000000 134072890075294545372120586591549758898176 4288113847432992259883667554304000000000000))
theorem leaf00193_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 144189752093574699110761496576000000000000 134072890075294545372120586591549758898176 4288113847432992259883667554304000000000000 raw00193=true := by decide +kernel
#print axioms leaf00193_raw
theorem leaf00193_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00193=true := by decide +kernel
#print axioms leaf00193_rectangular
def affine00193 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00193 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/3200),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00193_transform : affine00193=(NestedInteger.clearedAll 3 raw00193 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/3200),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00193_transform
theorem leaf00193_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00193=true := by decide +kernel
#print axioms leaf00193_sign
theorem leaf00193_log : RationalLog.accepts (3872537809/4294967296) (-222337359/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00193_log
def leaf00193 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15633084247/500000000000) (3872537809/4294967296) (-222337359/4294967296) 1 8 ![60,0,4] ![(13/3200),0,(1/4)] ![(3/32000),1,(1/4)] affine00193
theorem leaf00193_checked : FastNestedCellData.accepts 1 2 4 leaf00193=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15633084247/500000000000) (3872537809/4294967296) (-222337359/4294967296) 1 8 ![60,0,4] ![(13/3200),0,(1/4)] ![(3/32000),1,(1/4)] 144189752093574699110761496576000000000000 134072890075294545372120586591549758898176 4288113847432992259883667554304000000000000 raw00193 affine00193
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00193_raw leaf00193_rectangular
    leaf00193_transform leaf00193_sign leaf00193_log
#print axioms leaf00193_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
