/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00730 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4043928953493790420360499298304000000000000 150895039201550090451122598194988642729984 172080308664826719233674051584000000000000))
theorem leaf00730_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4043928953493790420360499298304000000000000 150895039201550090451122598194988642729984 172080308664826719233674051584000000000000 raw00730=true := by decide +kernel
#print axioms leaf00730_raw
theorem leaf00730_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00730=true := by decide +kernel
#print axioms leaf00730_rectangular
def affine00730 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00730 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(203/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00730_transform : affine00730=(NestedInteger.clearedAll 3 raw00730 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(203/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00730_transform
theorem leaf00730_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00730=true := by decide +kernel
#print axioms leaf00730_sign
theorem leaf00730_log : RationalLog.accepts (42693633/2147483648) (-2103461489/1073741824) 6 8=true := by decide +kernel
#print axioms leaf00730_log
def leaf00730 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (876887311351/1000000000000) (42693633/2147483648) (-2103461489/1073741824) 6 8 ![60,0,4] ![(203/6400),0,0] ![(3/6400),1,(1/16)] affine00730
theorem leaf00730_checked : FastNestedCellData.accepts 1 2 4 leaf00730=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (876887311351/1000000000000) (42693633/2147483648) (-2103461489/1073741824) 6 8 ![60,0,4] ![(203/6400),0,0] ![(3/6400),1,(1/16)] 4043928953493790420360499298304000000000000 150895039201550090451122598194988642729984 172080308664826719233674051584000000000000 raw00730 affine00730
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00730_raw leaf00730_rectangular
    leaf00730_transform leaf00730_sign leaf00730_log
#print axioms leaf00730_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
