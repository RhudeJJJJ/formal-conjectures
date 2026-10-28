/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5242 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap5242 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,16,13,14,15,7,8,9,10,11,12] (sourceLabel 7 2 5 v)
def fusedMap5242 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5242_checked : acceptsGraphIso
    (source (graph core5242) (root 7) 2 5) DegreeTwoThreeSpectrum5956.graph sourceMap5242=true := by decide +kernel
theorem fusedMap5242_checked : acceptsGraphIso
    (fused (graph core5242) (root 7) 2 5) DegreeTwoThreeSpectrum4964.graph fusedMap5242=true := by decide +kernel
theorem certified5242 : Certified (graph core5242) (root 7) 2 5 :=
  of_native_maps core5242 DegreeTwoThreeSpectrum5956.graph DegreeTwoThreeSpectrum4964.graph
    sourceMap5242 fusedMap5242 sourceMap5242_checked fusedMap5242_checked
    DegreeTwoThreeFiniteComparisons.comparison5242
#print axioms sourceMap5242_checked
#print axioms fusedMap5242_checked
#print axioms certified5242
def sourceMap5242swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,16,7,8,9,10,11,12,13,14,15] (sourceLabel 7 5 2 v)
def fusedMap5242swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5242swap_checked : acceptsGraphIso
    (source (graph core5242) (root 7) 5 2) DegreeTwoThreeSpectrum5956.graph sourceMap5242swap=true := by decide +kernel
theorem fusedMap5242swap_checked : acceptsGraphIso
    (fused (graph core5242) (root 7) 5 2) DegreeTwoThreeSpectrum4964.graph fusedMap5242swap=true := by decide +kernel
theorem certified5242swap : Certified (graph core5242) (root 7) 5 2 :=
  of_native_maps core5242 DegreeTwoThreeSpectrum5956.graph DegreeTwoThreeSpectrum4964.graph
    sourceMap5242swap fusedMap5242swap sourceMap5242swap_checked fusedMap5242swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5242
#print axioms sourceMap5242swap_checked
#print axioms fusedMap5242swap_checked
#print axioms certified5242swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
