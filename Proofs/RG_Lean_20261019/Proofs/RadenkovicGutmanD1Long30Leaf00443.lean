/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00443 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 24618318916767210652756344832000000000000 20337704056359990771974744616232491679744 238113094157470739157219278848000000000000))
theorem leaf00443_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 24618318916767210652756344832000000000000 20337704056359990771974744616232491679744 238113094157470739157219278848000000000000 raw00443=true := by decide +kernel
#print axioms leaf00443_raw
theorem leaf00443_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00443=true := by decide +kernel
#print axioms leaf00443_rectangular
def affine00443 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00443 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00443_transform : affine00443=(NestedInteger.clearedAll 3 raw00443 (IntegerComputedClassCell.leftNumerator ![(9/800),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/800),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00443_transform
theorem leaf00443_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00443=true := by decide +kernel
#print axioms leaf00443_sign
theorem leaf00443_log : RationalLog.accepts (3268953869/4294967296) (-146551769/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00443_log
def leaf00443 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10676493941/125000000000) (3268953869/4294967296) (-146551769/1073741824) 1 8 ![60,0,4] ![(9/800),0,(1/4)] ![(1/6400),1,(1/4)] affine00443
theorem leaf00443_checked : FastNestedCellData.accepts 1 2 4 leaf00443=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10676493941/125000000000) (3268953869/4294967296) (-146551769/1073741824) 1 8 ![60,0,4] ![(9/800),0,(1/4)] ![(1/6400),1,(1/4)] 24618318916767210652756344832000000000000 20337704056359990771974744616232491679744 238113094157470739157219278848000000000000 raw00443 affine00443
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00443_raw leaf00443_rectangular
    leaf00443_transform leaf00443_sign leaf00443_log
#print axioms leaf00443_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
