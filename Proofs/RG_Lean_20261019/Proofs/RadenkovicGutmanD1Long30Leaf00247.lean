/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00247 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 23339909215906247590828572672000000000000 19387484556297105103704149774103465689088 239420895540104707120379723776000000000000))
theorem leaf00247_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 23339909215906247590828572672000000000000 19387484556297105103704149774103465689088 239420895540104707120379723776000000000000 raw00247=true := by decide +kernel
#print axioms leaf00247_raw
theorem leaf00247_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00247=true := by decide +kernel
#print axioms leaf00247_rectangular
def affine00247 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00247 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(33/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00247_transform : affine00247=(NestedInteger.clearedAll 3 raw00247 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(33/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00247_transform
theorem leaf00247_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00247=true := by decide +kernel
#print axioms leaf00247_sign
theorem leaf00247_log : RationalLog.accepts (3300394693/4294967296) (-565651257/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00247_log
def leaf00247 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10122072111/125000000000) (3300394693/4294967296) (-565651257/4294967296) 1 8 ![60,0,4] ![(33/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00247
theorem leaf00247_checked : FastNestedCellData.accepts 1 2 4 leaf00247=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10122072111/125000000000) (3300394693/4294967296) (-565651257/4294967296) 1 8 ![60,0,4] ![(33/6400),0,(1/8)] ![(1/6400),1,(1/8)] 23339909215906247590828572672000000000000 19387484556297105103704149774103465689088 239420895540104707120379723776000000000000 raw00247 affine00247
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00247_raw leaf00247_rectangular
    leaf00247_transform leaf00247_sign leaf00247_log
#print axioms leaf00247_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
