/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00721 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11315563556215711694925594624000000000000 3043429587229797615158970839815906394112 4845145639236837439849889792000000000000))
theorem leaf00721_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11315563556215711694925594624000000000000 3043429587229797615158970839815906394112 4845145639236837439849889792000000000000 raw00721=true := by decide +kernel
#print axioms leaf00721_raw
theorem leaf00721_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00721=true := by decide +kernel
#print axioms leaf00721_rectangular
def affine00721 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00721 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(197/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00721_transform : affine00721=(NestedInteger.clearedAll 3 raw00721 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(197/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00721_transform
theorem leaf00721_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00721=true := by decide +kernel
#print axioms leaf00721_sign
theorem leaf00721_log : RationalLog.accepts (88688071/536870912) (-1933414247/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00721_log
def leaf00721 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (157034989959/250000000000) (88688071/536870912) (-1933414247/2147483648) 3 8 ![60,0,4] ![(197/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00721
theorem leaf00721_checked : FastNestedCellData.accepts 1 2 4 leaf00721=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (157034989959/250000000000) (88688071/536870912) (-1933414247/2147483648) 3 8 ![60,0,4] ![(197/6400),0,(1/16)] ![(3/6400),1,(1/16)] 11315563556215711694925594624000000000000 3043429587229797615158970839815906394112 4845145639236837439849889792000000000000 raw00721 affine00721
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00721_raw leaf00721_rectangular
    leaf00721_transform leaf00721_sign leaf00721_log
#print axioms leaf00721_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
