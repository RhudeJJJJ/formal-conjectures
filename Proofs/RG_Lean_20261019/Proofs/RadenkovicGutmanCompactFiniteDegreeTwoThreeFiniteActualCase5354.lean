/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5354 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5354 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,6,7,8,9,2,3,4,5,0,10,11,12,13,14] (sourceLabel 4 3 5 v)
def fusedMap5354 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 3 5 v)
theorem sourceMap5354_checked : acceptsGraphIso
    (source (graph core5354) (root 4) 3 5) DegreeTwoThreeSpectrum2956.graph sourceMap5354=true := by decide +kernel
theorem fusedMap5354_checked : acceptsGraphIso
    (fused (graph core5354) (root 4) 3 5) DegreeTwoThreeSpectrum2311.graph fusedMap5354=true := by decide +kernel
theorem certified5354 : Certified (graph core5354) (root 4) 3 5 :=
  of_native_maps core5354 DegreeTwoThreeSpectrum2956.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap5354 fusedMap5354 sourceMap5354_checked fusedMap5354_checked
    DegreeTwoThreeFiniteComparisons.comparison5354
#print axioms sourceMap5354_checked
#print axioms fusedMap5354_checked
#print axioms certified5354
def sourceMap5354swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,6,7,8,9,0,10,11,12,13,14,2,3,4,5] (sourceLabel 4 5 3 v)
def fusedMap5354swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13,14] (fusedLabel 4 5 3 v)
theorem sourceMap5354swap_checked : acceptsGraphIso
    (source (graph core5354) (root 4) 5 3) DegreeTwoThreeSpectrum2956.graph sourceMap5354swap=true := by decide +kernel
theorem fusedMap5354swap_checked : acceptsGraphIso
    (fused (graph core5354) (root 4) 5 3) DegreeTwoThreeSpectrum2311.graph fusedMap5354swap=true := by decide +kernel
theorem certified5354swap : Certified (graph core5354) (root 4) 5 3 :=
  of_native_maps core5354 DegreeTwoThreeSpectrum2956.graph DegreeTwoThreeSpectrum2311.graph
    sourceMap5354swap fusedMap5354swap sourceMap5354swap_checked fusedMap5354swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5354
#print axioms sourceMap5354swap_checked
#print axioms fusedMap5354swap_checked
#print axioms certified5354swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
