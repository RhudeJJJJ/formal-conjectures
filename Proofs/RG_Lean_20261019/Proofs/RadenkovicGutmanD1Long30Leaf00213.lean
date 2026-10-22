/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00213 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2457909428244231624910176256000000000000 2270987160758899531548940369109694021632 66577665155142160379744878592000000000000))
theorem leaf00213_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2457909428244231624910176256000000000000 2270987160758899531548940369109694021632 66577665155142160379744878592000000000000 raw00213=true := by decide +kernel
#print axioms leaf00213_raw
theorem leaf00213_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00213=true := by decide +kernel
#print axioms leaf00213_rectangular
def affine00213 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00213 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/16000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00213_transform : affine00213=(NestedInteger.clearedAll 3 raw00213 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/16000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00213_transform
theorem leaf00213_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00213=true := by decide +kernel
#print axioms leaf00213_sign
theorem leaf00213_log : RationalLog.accepts (1918720811/2147483648) (-120944193/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00213_log
def leaf00213 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4263793187/125000000000) (1918720811/2147483648) (-120944193/2147483648) 1 8 ![60,0,4] ![(71/16000),0,(1/4)] ![(3/32000),1,(1/4)] affine00213
theorem leaf00213_checked : FastNestedCellData.accepts 1 2 4 leaf00213=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4263793187/125000000000) (1918720811/2147483648) (-120944193/2147483648) 1 8 ![60,0,4] ![(71/16000),0,(1/4)] ![(3/32000),1,(1/4)] 2457909428244231624910176256000000000000 2270987160758899531548940369109694021632 66577665155142160379744878592000000000000 raw00213 affine00213
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00213_raw leaf00213_rectangular
    leaf00213_transform leaf00213_sign leaf00213_log
#print axioms leaf00213_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
