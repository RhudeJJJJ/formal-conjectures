/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00680 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16007647943513081198101598830592000000000000 433805006712605509426841158695245863452672 499904168617359284784863379456000000000000))
theorem leaf00680_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16007647943513081198101598830592000000000000 433805006712605509426841158695245863452672 499904168617359284784863379456000000000000 raw00680=true := by decide +kernel
#print axioms leaf00680_raw
theorem leaf00680_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00680=true := by decide +kernel
#print axioms leaf00680_rectangular
def affine00680 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00680 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(173/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00680_transform : affine00680=(NestedInteger.clearedAll 3 raw00680 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(173/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00680_transform
theorem leaf00680_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00680=true := by decide +kernel
#print axioms leaf00680_sign
theorem leaf00680_log : RationalLog.accepts (62316353/4294967296) (-4545122787/2147483648) 7 8=true := by decide +kernel
#print axioms leaf00680_log
def leaf00680 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (867776333837/1000000000000) (62316353/4294967296) (-4545122787/2147483648) 7 8 ![60,0,4] ![(173/6400),0,0] ![(3/6400),1,(1/16)] affine00680
theorem leaf00680_checked : FastNestedCellData.accepts 1 2 4 leaf00680=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (867776333837/1000000000000) (62316353/4294967296) (-4545122787/2147483648) 7 8 ![60,0,4] ![(173/6400),0,0] ![(3/6400),1,(1/16)] 16007647943513081198101598830592000000000000 433805006712605509426841158695245863452672 499904168617359284784863379456000000000000 raw00680 affine00680
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00680_raw leaf00680_rectangular
    leaf00680_transform leaf00680_sign leaf00680_log
#print axioms leaf00680_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
