/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00662 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1560243655390633904002039808000000000000 765275680719244997453656756184797937664 2208946826103263287069114368000000000000))
theorem leaf00662_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1560243655390633904002039808000000000000 765275680719244997453656756184797937664 2208946826103263287069114368000000000000 raw00662=true := by decide +kernel
#print axioms leaf00662_raw
theorem leaf00662_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00662=true := by decide +kernel
#print axioms leaf00662_rectangular
def affine00662 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00662 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(161/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00662_transform : affine00662=(NestedInteger.clearedAll 3 raw00662 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(161/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00662_transform
theorem leaf00662_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00662=true := by decide +kernel
#print axioms leaf00662_sign
theorem leaf00662_log : RationalLog.accepts (782288883/2147483648) (-542147271/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00662_log
def leaf00662 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10826365189/31250000000) (782288883/2147483648) (-542147271/1073741824) 2 8 ![60,0,4] ![(161/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00662
theorem leaf00662_checked : FastNestedCellData.accepts 1 2 4 leaf00662=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10826365189/31250000000) (782288883/2147483648) (-542147271/1073741824) 2 8 ![60,0,4] ![(161/6400),0,(1/8)] ![(3/6400),1,(1/8)] 1560243655390633904002039808000000000000 765275680719244997453656756184797937664 2208946826103263287069114368000000000000 raw00662 affine00662
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00662_raw leaf00662_rectangular
    leaf00662_transform leaf00662_sign leaf00662_log
#print axioms leaf00662_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
