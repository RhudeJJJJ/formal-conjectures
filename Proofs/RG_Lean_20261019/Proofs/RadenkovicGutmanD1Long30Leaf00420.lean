/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00420 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16540116289049179475972980736000000000000 61556114276321597559396840017982652416 89390453601026136575311872000000000000))
theorem leaf00420_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16540116289049179475972980736000000000000 61556114276321597559396840017982652416 89390453601026136575311872000000000000 raw00420=true := by decide +kernel
#print axioms leaf00420_raw
theorem leaf00420_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00420=true := by decide +kernel
#print axioms leaf00420_rectangular
def affine00420 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00420 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/1600),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00420_transform : affine00420=(NestedInteger.clearedAll 3 raw00420 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/1600),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00420_transform
theorem leaf00420_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00420=true := by decide +kernel
#print axioms leaf00420_sign
theorem leaf00420_log : RationalLog.accepts (9465867/4294967296) (-13137246221/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00420_log
def leaf00420 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (43038792033/62500000000) (9465867/4294967296) (-13137246221/4294967296) 9 8 ![60,0,4] ![(17/1600),0,0] ![(1/6400),1,(1/16)] affine00420
theorem leaf00420_checked : FastNestedCellData.accepts 1 2 4 leaf00420=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (43038792033/62500000000) (9465867/4294967296) (-13137246221/4294967296) 9 8 ![60,0,4] ![(17/1600),0,0] ![(1/6400),1,(1/16)] 16540116289049179475972980736000000000000 61556114276321597559396840017982652416 89390453601026136575311872000000000000 raw00420 affine00420
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00420_raw leaf00420_rectangular
    leaf00420_transform leaf00420_sign leaf00420_log
#print axioms leaf00420_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
