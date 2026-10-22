/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00442 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 197544761449104662374274564096000000000000 135716476865690729950763855434576992141312 792075899963793604857846300672000000000000))
theorem leaf00442_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 197544761449104662374274564096000000000000 135716476865690729950763855434576992141312 792075899963793604857846300672000000000000 raw00442=true := by decide +kernel
#print axioms leaf00442_raw
theorem leaf00442_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00442=true := by decide +kernel
#print axioms leaf00442_rectangular
def affine00442 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00442 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00442_transform : affine00442=(NestedInteger.clearedAll 3 raw00442 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00442_transform
theorem leaf00442_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00442=true := by decide +kernel
#print axioms leaf00442_sign
theorem leaf00442_log : RationalLog.accepts (629771393/1073741824) (-71611599/268435456) 1 8=true := by decide +kernel
#print axioms leaf00442_log
def leaf00442 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (171342767621/1000000000000) (629771393/1073741824) (-71611599/268435456) 1 8 ![60,0,4] ![(9/800),0,(1/8)] ![(1/6400),1,(1/8)] affine00442
theorem leaf00442_checked : FastNestedCellData.accepts 1 2 4 leaf00442=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (171342767621/1000000000000) (629771393/1073741824) (-71611599/268435456) 1 8 ![60,0,4] ![(9/800),0,(1/8)] ![(1/6400),1,(1/8)] 197544761449104662374274564096000000000000 135716476865690729950763855434576992141312 792075899963793604857846300672000000000000 raw00442 affine00442
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00442_raw leaf00442_rectangular
    leaf00442_transform leaf00442_sign leaf00442_log
#print axioms leaf00442_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
