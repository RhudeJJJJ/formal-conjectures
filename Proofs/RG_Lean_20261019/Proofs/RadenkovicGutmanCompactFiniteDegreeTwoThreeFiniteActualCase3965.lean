/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3965 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap3965 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3965 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3965_checked : acceptsGraphIso
    (source (graph core3965) (root 7) 1 5) DegreeTwoThreeSpectrum4604.graph sourceMap3965=true := by decide +kernel
theorem fusedMap3965_checked : acceptsGraphIso
    (fused (graph core3965) (root 7) 1 5) DegreeTwoThreeSpectrum4086.graph fusedMap3965=true := by decide +kernel
theorem certified3965 : Certified (graph core3965) (root 7) 1 5 :=
  of_native_maps core3965 DegreeTwoThreeSpectrum4604.graph DegreeTwoThreeSpectrum4086.graph
    sourceMap3965 fusedMap3965 sourceMap3965_checked fusedMap3965_checked
    DegreeTwoThreeFiniteComparisons.comparison3965
#print axioms sourceMap3965_checked
#print axioms fusedMap3965_checked
#print axioms certified3965
def sourceMap3965swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3965swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3965swap_checked : acceptsGraphIso
    (source (graph core3965) (root 7) 5 1) DegreeTwoThreeSpectrum4604.graph sourceMap3965swap=true := by decide +kernel
theorem fusedMap3965swap_checked : acceptsGraphIso
    (fused (graph core3965) (root 7) 5 1) DegreeTwoThreeSpectrum4086.graph fusedMap3965swap=true := by decide +kernel
theorem certified3965swap : Certified (graph core3965) (root 7) 5 1 :=
  of_native_maps core3965 DegreeTwoThreeSpectrum4604.graph DegreeTwoThreeSpectrum4086.graph
    sourceMap3965swap fusedMap3965swap sourceMap3965swap_checked fusedMap3965swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3965
#print axioms sourceMap3965swap_checked
#print axioms fusedMap3965swap_checked
#print axioms certified3965swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
