/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallKeysData
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0500
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0501
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0502
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0503
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0504
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0505
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0506
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0507
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0508
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0509
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0510
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0511
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0512
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0513
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0514
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0515
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0516
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0517
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0518
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0519
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0520
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0521
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0522
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0523
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0524
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0525
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0526
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0527
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0528
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0529
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0530
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0531
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0532
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0533
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0534
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0535
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0536
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0537
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0538
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0539
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0540
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0541
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0542
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0543
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0544
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0545
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0546
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0547
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0548
import Proofs.RadenkovicGutmanDegreeOneSmallActualCase0549
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneSmallActualCases
theorem certified_keys10 : ∀ k ∈ keys10, Certified k := by
  apply certified_cons (by exact certified0500)
  apply certified_cons (by exact certified0500swap)
  apply certified_cons (by exact certified0501)
  apply certified_cons (by exact certified0502)
  apply certified_cons (by exact certified0502swap)
  apply certified_cons (by exact certified0503)
  apply certified_cons (by exact certified0503swap)
  apply certified_cons (by exact certified0504)
  apply certified_cons (by exact certified0504swap)
  apply certified_cons (by exact certified0505)
  apply certified_cons (by exact certified0506)
  apply certified_cons (by exact certified0506swap)
  apply certified_cons (by exact certified0507)
  apply certified_cons (by exact certified0508)
  apply certified_cons (by exact certified0508swap)
  apply certified_cons (by exact certified0509)
  apply certified_cons (by exact certified0509swap)
  apply certified_cons (by exact certified0510)
  apply certified_cons (by exact certified0510swap)
  apply certified_cons (by exact certified0511)
  apply certified_cons (by exact certified0512)
  apply certified_cons (by exact certified0512swap)
  apply certified_cons (by exact certified0513)
  apply certified_cons (by exact certified0514)
  apply certified_cons (by exact certified0514swap)
  apply certified_cons (by exact certified0515)
  apply certified_cons (by exact certified0515swap)
  apply certified_cons (by exact certified0516)
  apply certified_cons (by exact certified0516swap)
  apply certified_cons (by exact certified0517)
  apply certified_cons (by exact certified0518)
  apply certified_cons (by exact certified0518swap)
  apply certified_cons (by exact certified0519)
  apply certified_cons (by exact certified0520)
  apply certified_cons (by exact certified0520swap)
  apply certified_cons (by exact certified0521)
  apply certified_cons (by exact certified0521swap)
  apply certified_cons (by exact certified0522)
  apply certified_cons (by exact certified0522swap)
  apply certified_cons (by exact certified0523)
  apply certified_cons (by exact certified0524)
  apply certified_cons (by exact certified0524swap)
  apply certified_cons (by exact certified0525)
  apply certified_cons (by exact certified0526)
  apply certified_cons (by exact certified0526swap)
  apply certified_cons (by exact certified0527)
  apply certified_cons (by exact certified0527swap)
  apply certified_cons (by exact certified0528)
  apply certified_cons (by exact certified0528swap)
  apply certified_cons (by exact certified0529)
  apply certified_cons (by exact certified0530)
  apply certified_cons (by exact certified0530swap)
  apply certified_cons (by exact certified0531)
  apply certified_cons (by exact certified0532)
  apply certified_cons (by exact certified0532swap)
  apply certified_cons (by exact certified0533)
  apply certified_cons (by exact certified0533swap)
  apply certified_cons (by exact certified0534)
  apply certified_cons (by exact certified0534swap)
  apply certified_cons (by exact certified0535)
  apply certified_cons (by exact certified0536)
  apply certified_cons (by exact certified0536swap)
  apply certified_cons (by exact certified0537)
  apply certified_cons (by exact certified0538)
  apply certified_cons (by exact certified0538swap)
  apply certified_cons (by exact certified0539)
  apply certified_cons (by exact certified0539swap)
  apply certified_cons (by exact certified0540)
  apply certified_cons (by exact certified0540swap)
  apply certified_cons (by exact certified0541)
  apply certified_cons (by exact certified0542)
  apply certified_cons (by exact certified0542swap)
  apply certified_cons (by exact certified0543)
  apply certified_cons (by exact certified0544)
  apply certified_cons (by exact certified0544swap)
  apply certified_cons (by exact certified0545)
  apply certified_cons (by exact certified0545swap)
  apply certified_cons (by exact certified0546)
  apply certified_cons (by exact certified0546swap)
  apply certified_cons (by exact certified0547)
  apply certified_cons (by exact certified0548)
  apply certified_cons (by exact certified0548swap)
  apply certified_cons (by exact certified0549)
  simp
#print axioms certified_keys10
end Gebendorfer.RadenkovicGutman.DegreeOneSmallKeys
