/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5291 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap5291 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5291 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5291_checked : acceptsGraphIso
    (source (graph core5291) (root 6) 2 6) DegreeTwoThreeSpectrum5365.graph sourceMap5291=true := by decide +kernel
theorem fusedMap5291_checked : acceptsGraphIso
    (fused (graph core5291) (root 6) 2 6) DegreeTwoThreeSpectrum4993.graph fusedMap5291=true := by decide +kernel
theorem certified5291 : Certified (graph core5291) (root 6) 2 6 :=
  of_native_maps core5291 DegreeTwoThreeSpectrum5365.graph DegreeTwoThreeSpectrum4993.graph
    sourceMap5291 fusedMap5291 sourceMap5291_checked fusedMap5291_checked
    DegreeTwoThreeFiniteComparisons.comparison5291
#print axioms sourceMap5291_checked
#print axioms fusedMap5291_checked
#print axioms certified5291
def sourceMap5291swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,15,16,7,8,9] (sourceLabel 6 6 2 v)
def fusedMap5291swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5291swap_checked : acceptsGraphIso
    (source (graph core5291) (root 6) 6 2) DegreeTwoThreeSpectrum5365.graph sourceMap5291swap=true := by decide +kernel
theorem fusedMap5291swap_checked : acceptsGraphIso
    (fused (graph core5291) (root 6) 6 2) DegreeTwoThreeSpectrum4993.graph fusedMap5291swap=true := by decide +kernel
theorem certified5291swap : Certified (graph core5291) (root 6) 6 2 :=
  of_native_maps core5291 DegreeTwoThreeSpectrum5365.graph DegreeTwoThreeSpectrum4993.graph
    sourceMap5291swap fusedMap5291swap sourceMap5291swap_checked fusedMap5291swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5291
#print axioms sourceMap5291swap_checked
#print axioms fusedMap5291swap_checked
#print axioms certified5291swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
