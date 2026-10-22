/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00440 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 813861811657915108632289083392000000000000 3444752450193330953178564922642249285632 4879856900749071070261149696000000000000))
theorem leaf00440_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 813861811657915108632289083392000000000000 3444752450193330953178564922642249285632 4879856900749071070261149696000000000000 raw00440=true := by decide +kernel
#print axioms leaf00440_raw
theorem leaf00440_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00440=true := by decide +kernel
#print axioms leaf00440_rectangular
def affine00440 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00440 (IntegerComputedClassCell.leftNumerator ![(9/800),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/800),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00440_transform : affine00440=(NestedInteger.clearedAll 3 raw00440 (IntegerComputedClassCell.leftNumerator ![(9/800),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/800),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/800),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00440_transform
theorem leaf00440_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00440=true := by decide +kernel
#print axioms leaf00440_sign
theorem leaf00440_log : RationalLog.accepts (5328199/2147483648) (-201294343/67108864) 9 8=true := by decide +kernel
#print axioms leaf00440_log
def leaf00440 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (352956297721/500000000000) (5328199/2147483648) (-201294343/67108864) 9 8 ![60,0,4] ![(9/800),0,0] ![(1/6400),1,(1/16)] affine00440
theorem leaf00440_checked : FastNestedCellData.accepts 1 2 4 leaf00440=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (352956297721/500000000000) (5328199/2147483648) (-201294343/67108864) 9 8 ![60,0,4] ![(9/800),0,0] ![(1/6400),1,(1/16)] 813861811657915108632289083392000000000000 3444752450193330953178564922642249285632 4879856900749071070261149696000000000000 raw00440 affine00440
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00440_raw leaf00440_rectangular
    leaf00440_transform leaf00440_sign leaf00440_log
#print axioms leaf00440_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
