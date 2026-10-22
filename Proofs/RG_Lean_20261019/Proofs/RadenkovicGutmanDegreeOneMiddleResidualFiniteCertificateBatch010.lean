/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteKeysData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0500
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0501
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0502
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0503
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0504
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0505
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0506
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0507
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0508
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0509
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0510
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0511
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0512
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0513
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0514
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0515
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0516
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0517
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0518
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0519
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0520
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0521
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0522
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0523
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0524
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0525
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0526
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0527
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0528
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0529
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0530
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0531
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0532
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0533
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0534
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0535
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0536
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0537
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0538
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0539
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0540
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0541
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0542
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0543
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0544
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0545
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0546
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0547
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0548
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteActualCase0549
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
open SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneMiddleResidualFiniteActualCases
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
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteKeys
