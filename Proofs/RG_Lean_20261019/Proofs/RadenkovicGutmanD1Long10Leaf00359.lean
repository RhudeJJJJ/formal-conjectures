/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00359 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 864481190949219523126089482240000000000 665221284266122348857256493214452416512 1774354218419653542462200217600000000000))
theorem leaf00359_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 864481190949219523126089482240000000000 665221284266122348857256493214452416512 1774354218419653542462200217600000000000 raw00359=true := by decide +kernel
#print axioms leaf00359_raw
theorem leaf00359_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00359=true := by decide +kernel
#print axioms leaf00359_rectangular
def affine00359 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00359 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf00359_transform : affine00359=(NestedInteger.clearedAll 3 raw00359 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00359_transform
theorem leaf00359_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00359=true := by decide +kernel
#print axioms leaf00359_sign
theorem leaf00359_log : RationalLog.accepts (2403789915/4294967296) (-1246393785/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00359_log
def leaf00359 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (9372723853/25000000000) (2403789915/4294967296) (-1246393785/4294967296) 1 8 ![52,0,4] ![(1/5),0,(1/2)] ![(3/160),1,(1/2)] affine00359
theorem leaf00359_checked : FastNestedCellData.accepts 1 0 4 leaf00359=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (9372723853/25000000000) (2403789915/4294967296) (-1246393785/4294967296) 1 8 ![52,0,4] ![(1/5),0,(1/2)] ![(3/160),1,(1/2)] 864481190949219523126089482240000000000 665221284266122348857256493214452416512 1774354218419653542462200217600000000000 raw00359 affine00359
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00359_raw leaf00359_rectangular
    leaf00359_transform leaf00359_sign leaf00359_log
#print axioms leaf00359_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
