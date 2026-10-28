/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5365 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5365 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,6,7,8,9,2,3,4,5,0,10,11,12,13,14,15] (sourceLabel 4 3 6 v)
def fusedMap5365 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 3 6 v)
theorem sourceMap5365_checked : acceptsGraphIso
    (source (graph core5365) (root 4) 3 6) DegreeTwoThreeSpectrum4118.graph sourceMap5365=true := by decide +kernel
theorem fusedMap5365_checked : acceptsGraphIso
    (fused (graph core5365) (root 4) 3 6) DegreeTwoThreeSpectrum3876.graph fusedMap5365=true := by decide +kernel
theorem certified5365 : Certified (graph core5365) (root 4) 3 6 :=
  of_native_maps core5365 DegreeTwoThreeSpectrum4118.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap5365 fusedMap5365 sourceMap5365_checked fusedMap5365_checked
    DegreeTwoThreeFiniteComparisons.comparison5365
#print axioms sourceMap5365_checked
#print axioms fusedMap5365_checked
#print axioms certified5365
def sourceMap5365swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,6,7,8,9,0,10,11,12,13,14,15,2,3,4,5] (sourceLabel 4 6 3 v)
def fusedMap5365swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 6 3 v)
theorem sourceMap5365swap_checked : acceptsGraphIso
    (source (graph core5365) (root 4) 6 3) DegreeTwoThreeSpectrum4118.graph sourceMap5365swap=true := by decide +kernel
theorem fusedMap5365swap_checked : acceptsGraphIso
    (fused (graph core5365) (root 4) 6 3) DegreeTwoThreeSpectrum3876.graph fusedMap5365swap=true := by decide +kernel
theorem certified5365swap : Certified (graph core5365) (root 4) 6 3 :=
  of_native_maps core5365 DegreeTwoThreeSpectrum4118.graph DegreeTwoThreeSpectrum3876.graph
    sourceMap5365swap fusedMap5365swap sourceMap5365swap_checked fusedMap5365swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5365
#print axioms sourceMap5365swap_checked
#print axioms fusedMap5365swap_checked
#print axioms certified5365swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
