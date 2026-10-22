/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00664 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 105918769671654898400072040448000000000000 86784419205023901067658050094581912961024 944644877168201829600186073088000000000000))
theorem leaf00664_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 105918769671654898400072040448000000000000 86784419205023901067658050094581912961024 944644877168201829600186073088000000000000 raw00664=true := by decide +kernel
#print axioms leaf00664_raw
theorem leaf00664_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00664=true := by decide +kernel
#print axioms leaf00664_rectangular
def affine00664 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00664 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(161/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00664_transform : affine00664=(NestedInteger.clearedAll 3 raw00664 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(161/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00664_transform
theorem leaf00664_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00664=true := by decide +kernel
#print axioms leaf00664_sign
theorem leaf00664_log : RationalLog.accepts (3222981451/4294967296) (-77077781/536870912) 1 8=true := by decide +kernel
#print axioms leaf00664_log
def leaf00664 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (22967472037/250000000000) (3222981451/4294967296) (-77077781/536870912) 1 8 ![60,0,4] ![(161/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00664
theorem leaf00664_checked : FastNestedCellData.accepts 1 2 4 leaf00664=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (22967472037/250000000000) (3222981451/4294967296) (-77077781/536870912) 1 8 ![60,0,4] ![(161/6400),0,(1/2)] ![(3/6400),1,(1/2)] 105918769671654898400072040448000000000000 86784419205023901067658050094581912961024 944644877168201829600186073088000000000000 raw00664 affine00664
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00664_raw leaf00664_rectangular
    leaf00664_transform leaf00664_sign leaf00664_log
#print axioms leaf00664_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
