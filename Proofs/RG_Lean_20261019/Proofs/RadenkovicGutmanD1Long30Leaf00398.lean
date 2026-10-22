/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00398 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7204823294365274841328648192000000000000 6084203407192900707257302055129035309056 81133252220551877500143140864000000000000))
theorem leaf00398_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7204823294365274841328648192000000000000 6084203407192900707257302055129035309056 81133252220551877500143140864000000000000 raw00398=true := by decide +kernel
#print axioms leaf00398_raw
theorem leaf00398_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00398=true := by decide +kernel
#print axioms leaf00398_rectangular
def affine00398 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00398 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(63/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00398_transform : affine00398=(NestedInteger.clearedAll 3 raw00398 (IntegerComputedClassCell.leftNumerator ![(63/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(63/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(63/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00398_transform
theorem leaf00398_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00398=true := by decide +kernel
#print axioms leaf00398_sign
theorem leaf00398_log : RationalLog.accepts (843481833/1073741824) (-129582659/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00398_log
def leaf00398 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (37495128327/500000000000) (843481833/1073741824) (-129582659/1073741824) 1 8 ![60,0,4] ![(63/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00398
theorem leaf00398_checked : FastNestedCellData.accepts 1 2 4 leaf00398=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (37495128327/500000000000) (843481833/1073741824) (-129582659/1073741824) 1 8 ![60,0,4] ![(63/6400),0,(1/4)] ![(1/6400),1,(1/4)] 7204823294365274841328648192000000000000 6084203407192900707257302055129035309056 81133252220551877500143140864000000000000 raw00398 affine00398
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00398_raw leaf00398_rectangular
    leaf00398_transform leaf00398_sign leaf00398_log
#print axioms leaf00398_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
