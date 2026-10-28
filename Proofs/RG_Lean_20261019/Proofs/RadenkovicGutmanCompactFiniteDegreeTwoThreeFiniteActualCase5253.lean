/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5253 : Family 7 := level7.get ⟨44,by decide⟩
def sourceMap5253 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5253 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5253_checked : acceptsGraphIso
    (source (graph core5253) (root 7) 2 5) DegreeTwoThreeSpectrum6660.graph sourceMap5253=true := by decide +kernel
theorem fusedMap5253_checked : acceptsGraphIso
    (fused (graph core5253) (root 7) 2 5) DegreeTwoThreeSpectrum5016.graph fusedMap5253=true := by decide +kernel
theorem certified5253 : Certified (graph core5253) (root 7) 2 5 :=
  of_native_maps core5253 DegreeTwoThreeSpectrum6660.graph DegreeTwoThreeSpectrum5016.graph
    sourceMap5253 fusedMap5253 sourceMap5253_checked fusedMap5253_checked
    DegreeTwoThreeFiniteComparisons.comparison5253
#print axioms sourceMap5253_checked
#print axioms fusedMap5253_checked
#print axioms certified5253
def sourceMap5253swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5253swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5253swap_checked : acceptsGraphIso
    (source (graph core5253) (root 7) 5 2) DegreeTwoThreeSpectrum6660.graph sourceMap5253swap=true := by decide +kernel
theorem fusedMap5253swap_checked : acceptsGraphIso
    (fused (graph core5253) (root 7) 5 2) DegreeTwoThreeSpectrum5016.graph fusedMap5253swap=true := by decide +kernel
theorem certified5253swap : Certified (graph core5253) (root 7) 5 2 :=
  of_native_maps core5253 DegreeTwoThreeSpectrum6660.graph DegreeTwoThreeSpectrum5016.graph
    sourceMap5253swap fusedMap5253swap sourceMap5253swap_checked fusedMap5253swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5253
#print axioms sourceMap5253swap_checked
#print axioms fusedMap5253swap_checked
#print axioms certified5253swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
