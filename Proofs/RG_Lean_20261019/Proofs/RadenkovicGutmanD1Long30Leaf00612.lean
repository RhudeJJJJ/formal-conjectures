/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00612 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 84817171885651679887562375168000000000000 45625281146031302098009782482200405475328 155046338546603421734245761024000000000000))
theorem leaf00612_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 84817171885651679887562375168000000000000 45625281146031302098009782482200405475328 155046338546603421734245761024000000000000 raw00612=true := by decide +kernel
#print axioms leaf00612_raw
theorem leaf00612_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00612=true := by decide +kernel
#print axioms leaf00612_rectangular
def affine00612 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00612 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00612_transform : affine00612=(NestedInteger.clearedAll 3 raw00612 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00612_transform
theorem leaf00612_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00612=true := by decide +kernel
#print axioms leaf00612_sign
theorem leaf00612_log : RationalLog.accepts (1785077953/4294967296) (-1885451749/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00612_log
def leaf00612 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (36783584809/125000000000) (1785077953/4294967296) (-1885451749/4294967296) 2 8 ![60,0,4] ![(131/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00612
theorem leaf00612_checked : FastNestedCellData.accepts 1 2 4 leaf00612=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (36783584809/125000000000) (1785077953/4294967296) (-1885451749/4294967296) 2 8 ![60,0,4] ![(131/6400),0,(1/8)] ![(3/6400),1,(1/8)] 84817171885651679887562375168000000000000 45625281146031302098009782482200405475328 155046338546603421734245761024000000000000 raw00612 affine00612
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00612_raw leaf00612_rectangular
    leaf00612_transform leaf00612_sign leaf00612_log
#print axioms leaf00612_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
