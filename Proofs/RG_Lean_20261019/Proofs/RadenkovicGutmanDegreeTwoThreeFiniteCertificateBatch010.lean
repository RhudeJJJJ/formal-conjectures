/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteKeysData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0500
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0501
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0502
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0503
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0504
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0505
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0506
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0507
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0508
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0509
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0510
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0511
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0512
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0513
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0514
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0515
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0516
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0517
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0518
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0519
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0520
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0521
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0522
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0523
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0524
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0525
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0526
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0527
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0528
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0529
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0530
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0531
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0532
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0533
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0534
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0535
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0536
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0537
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0538
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0539
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0540
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0541
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0542
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0543
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0544
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0545
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0546
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0547
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0548
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteActualCase0549
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeTwoThreeFiniteActualCases
theorem certified_keys010 : ∀ k ∈ keys010, Certified k := by
  apply certified_cons (by exact certified0500)
  apply certified_cons (by exact certified0501)
  apply certified_cons (by exact certified0502)
  apply certified_cons (by exact certified0503)
  apply certified_cons (by exact certified0504)
  apply certified_cons (by exact certified0505)
  apply certified_cons (by exact certified0506)
  apply certified_cons (by exact certified0507)
  apply certified_cons (by exact certified0508)
  apply certified_cons (by exact certified0509)
  apply certified_cons (by exact certified0510)
  apply certified_cons (by exact certified0511)
  apply certified_cons (by exact certified0512)
  apply certified_cons (by exact certified0513)
  apply certified_cons (by exact certified0514)
  apply certified_cons (by exact certified0515)
  apply certified_cons (by exact certified0516)
  apply certified_cons (by exact certified0517)
  apply certified_cons (by exact certified0518)
  apply certified_cons (by exact certified0519)
  apply certified_cons (by exact certified0520)
  apply certified_cons (by exact certified0521)
  apply certified_cons (by exact certified0522)
  apply certified_cons (by exact certified0523)
  apply certified_cons (by exact certified0524)
  apply certified_cons (by exact certified0525)
  apply certified_cons (by exact certified0526)
  apply certified_cons (by exact certified0527)
  apply certified_cons (by exact certified0528)
  apply certified_cons (by exact certified0529)
  apply certified_cons (by exact certified0530)
  apply certified_cons (by exact certified0531)
  apply certified_cons (by exact certified0532)
  apply certified_cons (by exact certified0533)
  apply certified_cons (by exact certified0534)
  apply certified_cons (by exact certified0535)
  apply certified_cons (by exact certified0536)
  apply certified_cons (by exact certified0537)
  apply certified_cons (by exact certified0538)
  apply certified_cons (by exact certified0539)
  apply certified_cons (by exact certified0540)
  apply certified_cons (by exact certified0541)
  apply certified_cons (by exact certified0542)
  apply certified_cons (by exact certified0543)
  apply certified_cons (by exact certified0544)
  apply certified_cons (by exact certified0545)
  apply certified_cons (by exact certified0546)
  apply certified_cons (by exact certified0547)
  apply certified_cons (by exact certified0548)
  apply certified_cons (by exact certified0549)
  simp
#print axioms certified_keys010
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteKeys
