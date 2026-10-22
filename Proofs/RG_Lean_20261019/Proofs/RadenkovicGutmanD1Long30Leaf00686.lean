/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00686 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1104861157282006449602445705216000000000 312069604881438945731409289711007563776 521030909312908758873643417600000000000))
theorem leaf00686_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1104861157282006449602445705216000000000 312069604881438945731409289711007563776 521030909312908758873643417600000000000 raw00686=true := by decide +kernel
#print axioms leaf00686_raw
theorem leaf00686_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00686=true := by decide +kernel
#print axioms leaf00686_rectangular
def affine00686 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00686 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00686_transform : affine00686=(NestedInteger.clearedAll 3 raw00686 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00686_transform
theorem leaf00686_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00686=true := by decide +kernel
#print axioms leaf00686_sign
theorem leaf00686_log : RationalLog.accepts (379349675/2147483648) (-465358011/536870912) 3 8=true := by decide +kernel
#print axioms leaf00686_log
def leaf00686 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (59894643351/100000000000) (379349675/2147483648) (-465358011/536870912) 3 8 ![60,0,4] ![(11/400),0,(1/16)] ![(3/6400),1,(1/16)] affine00686
theorem leaf00686_checked : FastNestedCellData.accepts 1 2 4 leaf00686=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (59894643351/100000000000) (379349675/2147483648) (-465358011/536870912) 3 8 ![60,0,4] ![(11/400),0,(1/16)] ![(3/6400),1,(1/16)] 1104861157282006449602445705216000000000 312069604881438945731409289711007563776 521030909312908758873643417600000000000 raw00686 affine00686
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00686_raw leaf00686_rectangular
    leaf00686_transform leaf00686_sign leaf00686_log
#print axioms leaf00686_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
