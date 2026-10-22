/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00286 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 715435746942985991926002483200000000000 459146809263598271434453057263387017216 2312228213861033280152797184000000000000))
theorem leaf00286_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 715435746942985991926002483200000000000 459146809263598271434453057263387017216 2312228213861033280152797184000000000000 raw00286=true := by decide +kernel
#print axioms leaf00286_raw
theorem leaf00286_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00286=true := by decide +kernel
#print axioms leaf00286_rectangular
def affine00286 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00286 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00286_transform : affine00286=(NestedInteger.clearedAll 3 raw00286 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00286_transform
theorem leaf00286_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00286=true := by decide +kernel
#print axioms leaf00286_sign
theorem leaf00286_log : RationalLog.accepts (287465815/536870912) (-1341433705/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00286_log
def leaf00286 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (49643327431/250000000000) (287465815/536870912) (-1341433705/4294967296) 1 8 ![60,0,4] ![(41/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00286
theorem leaf00286_checked : FastNestedCellData.accepts 1 2 4 leaf00286=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (49643327431/250000000000) (287465815/536870912) (-1341433705/4294967296) 1 8 ![60,0,4] ![(41/6400),0,(1/16)] ![(1/6400),1,(1/16)] 715435746942985991926002483200000000000 459146809263598271434453057263387017216 2312228213861033280152797184000000000000 raw00286 affine00286
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00286_raw leaf00286_rectangular
    leaf00286_transform leaf00286_sign leaf00286_log
#print axioms leaf00286_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
