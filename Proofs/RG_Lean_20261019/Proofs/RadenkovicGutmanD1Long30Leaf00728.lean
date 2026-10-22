/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00728 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4098799245229712371701994487808000000000000 2610997095381351211587024623567622000082944 11750854900189061735036263333888000000000000))
theorem leaf00728_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4098799245229712371701994487808000000000000 2610997095381351211587024623567622000082944 11750854900189061735036263333888000000000000 raw00728=true := by decide +kernel
#print axioms leaf00728_raw
theorem leaf00728_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00728=true := by decide +kernel
#print axioms leaf00728_rectangular
def affine00728 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00728 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00728_transform : affine00728=(NestedInteger.clearedAll 3 raw00728 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00728_transform
theorem leaf00728_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00728=true := by decide +kernel
#print axioms leaf00728_sign
theorem leaf00728_log : RationalLog.accepts (2238559381/4294967296) (-1399324895/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00728_log
def leaf00728 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (222196352313/1000000000000) (2238559381/4294967296) (-1399324895/4294967296) 1 8 ![60,0,4] ![(1/32),0,(1/4)] ![(3/6400),1,(1/4)] affine00728
theorem leaf00728_checked : FastNestedCellData.accepts 1 2 4 leaf00728=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (222196352313/1000000000000) (2238559381/4294967296) (-1399324895/4294967296) 1 8 ![60,0,4] ![(1/32),0,(1/4)] ![(3/6400),1,(1/4)] 4098799245229712371701994487808000000000000 2610997095381351211587024623567622000082944 11750854900189061735036263333888000000000000 raw00728 affine00728
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00728_raw leaf00728_rectangular
    leaf00728_transform leaf00728_sign leaf00728_log
#print axioms leaf00728_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
