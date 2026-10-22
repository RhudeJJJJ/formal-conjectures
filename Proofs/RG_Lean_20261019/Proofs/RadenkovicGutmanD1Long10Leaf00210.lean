/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00210 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 108063246441028910519135512821760000000000 3252484603587730720425833219730477940736 5552095931043941614748696576000000000000))
theorem leaf00210_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 108063246441028910519135512821760000000000 3252484603587730720425833219730477940736 5552095931043941614748696576000000000000 raw00210=true := by decide +kernel
#print axioms leaf00210_raw
theorem leaf00210_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00210=true := by decide +kernel
#print axioms leaf00210_rectangular
def affine00210 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00210 (IntegerComputedClassCell.leftNumerator ![(23/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/640),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00210_transform : affine00210=(NestedInteger.clearedAll 3 raw00210 (IntegerComputedClassCell.leftNumerator ![(23/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/640),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00210_transform
theorem leaf00210_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00210=true := by decide +kernel
#print axioms leaf00210_sign
theorem leaf00210_log : RationalLog.accepts (81516475/4294967296) (-4256735829/2147483648) 6 8=true := by decide +kernel
#print axioms leaf00210_log
def leaf00210 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (292906016393/500000000000) (81516475/4294967296) (-4256735829/2147483648) 6 8 ![52,0,4] ![(23/640),0,0] ![(3/3200),1,(1/4)] affine00210
theorem leaf00210_checked : FastNestedCellData.accepts 1 0 4 leaf00210=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (292906016393/500000000000) (81516475/4294967296) (-4256735829/2147483648) 6 8 ![52,0,4] ![(23/640),0,0] ![(3/3200),1,(1/4)] 108063246441028910519135512821760000000000 3252484603587730720425833219730477940736 5552095931043941614748696576000000000000 raw00210 affine00210
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00210_raw leaf00210_rectangular
    leaf00210_transform leaf00210_sign leaf00210_log
#print axioms leaf00210_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
