/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00894 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 621475281049008999241036595200000000000 423564301662458680132228390879280234496 1964424036086161305440039731200000000000))
theorem leaf00894_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 621475281049008999241036595200000000000 423564301662458680132228390879280234496 1964424036086161305440039731200000000000 raw00894=true := by decide +kernel
#print axioms leaf00894_raw
theorem leaf00894_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00894=true := by decide +kernel
#print axioms leaf00894_rectangular
def affine00894 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00894 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00894_transform : affine00894=(NestedInteger.clearedAll 3 raw00894 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00894_transform
theorem leaf00894_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00894=true := by decide +kernel
#print axioms leaf00894_sign
theorem leaf00894_log : RationalLog.accepts (150500661/268435456) (-621313231/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00894_log
def leaf00894 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (43123510391/200000000000) (150500661/268435456) (-621313231/2147483648) 1 8 ![60,0,4] ![(21/320),0,(1/2)] ![(1/640),1,(1/2)] affine00894
theorem leaf00894_checked : FastNestedCellData.accepts 1 2 4 leaf00894=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (43123510391/200000000000) (150500661/268435456) (-621313231/2147483648) 1 8 ![60,0,4] ![(21/320),0,(1/2)] ![(1/640),1,(1/2)] 621475281049008999241036595200000000000 423564301662458680132228390879280234496 1964424036086161305440039731200000000000 raw00894 affine00894
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00894_raw leaf00894_rectangular
    leaf00894_transform leaf00894_sign leaf00894_log
#print axioms leaf00894_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
