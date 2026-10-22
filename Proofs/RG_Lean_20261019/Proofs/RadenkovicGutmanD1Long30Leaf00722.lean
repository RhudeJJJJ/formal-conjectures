/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00722 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7214195345231823075608100864000000000000 3238443376771642413685877629437981229056 8086641232707319790657601536000000000000))
theorem leaf00722_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7214195345231823075608100864000000000000 3238443376771642413685877629437981229056 8086641232707319790657601536000000000000 raw00722=true := by decide +kernel
#print axioms leaf00722_raw
theorem leaf00722_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00722=true := by decide +kernel
#print axioms leaf00722_rectangular
def affine00722 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00722 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(197/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00722_transform : affine00722=(NestedInteger.clearedAll 3 raw00722 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(197/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00722_transform
theorem leaf00722_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00722=true := by decide +kernel
#print axioms leaf00722_sign
theorem leaf00722_log : RationalLog.accepts (43021447/134217728) (-2443330855/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00722_log
def leaf00722 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (400468288821/1000000000000) (43021447/134217728) (-2443330855/4294967296) 2 8 ![60,0,4] ![(197/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00722
theorem leaf00722_checked : FastNestedCellData.accepts 1 2 4 leaf00722=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (400468288821/1000000000000) (43021447/134217728) (-2443330855/4294967296) 2 8 ![60,0,4] ![(197/6400),0,(1/8)] ![(3/6400),1,(1/8)] 7214195345231823075608100864000000000000 3238443376771642413685877629437981229056 8086641232707319790657601536000000000000 raw00722 affine00722
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00722_raw leaf00722_rectangular
    leaf00722_transform leaf00722_sign leaf00722_log
#print axioms leaf00722_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
