/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch00
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch01
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch02
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch03
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch04
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch05
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch06
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch07
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch08
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch09
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch10
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch11
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch12
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch13
import Proofs.RadenkovicGutmanActualSmallGeFourCertificateBatch14
namespace Gebendorfer.RadenkovicGutman.SmallGeFourKeys
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certified_append {xs ys : List Key} (hx : ∀ k ∈ xs, Certified k)
    (hy : ∀ k ∈ ys, Certified k) : ∀ k ∈ xs++ys, Certified k := by
  intro k hk
  rcases List.mem_append.mp hk with h | h
  · exact hx k h
  · exact hy k h
theorem all_keys_certified : ∀ k ∈ keys, Certified k := by
  apply certified_append certified_keys00
  apply certified_append certified_keys01
  apply certified_append certified_keys02
  apply certified_append certified_keys03
  apply certified_append certified_keys04
  apply certified_append certified_keys05
  apply certified_append certified_keys06
  apply certified_append certified_keys07
  apply certified_append certified_keys08
  apply certified_append certified_keys09
  apply certified_append certified_keys10
  apply certified_append certified_keys11
  apply certified_append certified_keys12
  apply certified_append certified_keys13
  apply certified_append certified_keys14
  simp
#print axioms all_keys_certified
end Gebendorfer.RadenkovicGutman.SmallGeFourKeys
