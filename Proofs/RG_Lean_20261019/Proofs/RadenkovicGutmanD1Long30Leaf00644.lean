/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00644 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 983767625464945532136220262400000000000 816173396221648162754648011616607535104 9565102933197437628925450649600000000000))
theorem leaf00644_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 983767625464945532136220262400000000000 816173396221648162754648011616607535104 9565102933197437628925450649600000000000 raw00644=true := by decide +kernel
#print axioms leaf00644_raw
theorem leaf00644_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00644=true := by decide +kernel
#print axioms leaf00644_rectangular
def affine00644 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00644 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(149/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00644_transform : affine00644=(NestedInteger.clearedAll 3 raw00644 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(149/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00644_transform
theorem leaf00644_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00644=true := by decide +kernel
#print axioms leaf00644_sign
theorem leaf00644_log : RationalLog.accepts (1641567217/2147483648) (-288455771/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00644_log
def leaf00644 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4266411987/50000000000) (1641567217/2147483648) (-288455771/2147483648) 1 8 ![60,0,4] ![(149/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00644
theorem leaf00644_checked : FastNestedCellData.accepts 1 2 4 leaf00644=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4266411987/50000000000) (1641567217/2147483648) (-288455771/2147483648) 1 8 ![60,0,4] ![(149/6400),0,(1/2)] ![(3/6400),1,(1/2)] 983767625464945532136220262400000000000 816173396221648162754648011616607535104 9565102933197437628925450649600000000000 raw00644 affine00644
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00644_raw leaf00644_rectangular
    leaf00644_transform leaf00644_sign leaf00644_log
#print axioms leaf00644_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
