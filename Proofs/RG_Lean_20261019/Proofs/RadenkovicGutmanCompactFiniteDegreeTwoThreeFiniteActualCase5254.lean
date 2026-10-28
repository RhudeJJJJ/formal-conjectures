/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5254 : Family 7 := level7.get ⟨47,by decide⟩
def sourceMap5254 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,8,9,10,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5254 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5254_checked : acceptsGraphIso
    (source (graph core5254) (root 7) 2 5) DegreeTwoThreeSpectrum6734.graph sourceMap5254=true := by decide +kernel
theorem fusedMap5254_checked : acceptsGraphIso
    (fused (graph core5254) (root 7) 2 5) DegreeTwoThreeSpectrum5023.graph fusedMap5254=true := by decide +kernel
theorem certified5254 : Certified (graph core5254) (root 7) 2 5 :=
  of_native_maps core5254 DegreeTwoThreeSpectrum6734.graph DegreeTwoThreeSpectrum5023.graph
    sourceMap5254 fusedMap5254 sourceMap5254_checked fusedMap5254_checked
    DegreeTwoThreeFiniteComparisons.comparison5254
#print axioms sourceMap5254_checked
#print axioms fusedMap5254_checked
#print axioms certified5254
def sourceMap5254swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,11,0,12,13,14,15,16,8,9,10] (sourceLabel 7 5 2 v)
def fusedMap5254swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5254swap_checked : acceptsGraphIso
    (source (graph core5254) (root 7) 5 2) DegreeTwoThreeSpectrum6734.graph sourceMap5254swap=true := by decide +kernel
theorem fusedMap5254swap_checked : acceptsGraphIso
    (fused (graph core5254) (root 7) 5 2) DegreeTwoThreeSpectrum5023.graph fusedMap5254swap=true := by decide +kernel
theorem certified5254swap : Certified (graph core5254) (root 7) 5 2 :=
  of_native_maps core5254 DegreeTwoThreeSpectrum6734.graph DegreeTwoThreeSpectrum5023.graph
    sourceMap5254swap fusedMap5254swap sourceMap5254swap_checked fusedMap5254swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5254
#print axioms sourceMap5254swap_checked
#print axioms fusedMap5254swap_checked
#print axioms certified5254swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
