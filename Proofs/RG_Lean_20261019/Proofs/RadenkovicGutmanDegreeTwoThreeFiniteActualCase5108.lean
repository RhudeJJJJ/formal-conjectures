/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5108 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap5108 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,11,6,7,8,0,12,13,14,15] (sourceLabel 7 2 4 v)
def fusedMap5108 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 2 4 v)
theorem sourceMap5108_checked : acceptsGraphIso
    (source (graph core5108) (root 7) 2 4) DegreeTwoThreeSpectrum4766.graph sourceMap5108=true := by decide +kernel
theorem fusedMap5108_checked : acceptsGraphIso
    (fused (graph core5108) (root 7) 2 4) DegreeTwoThreeSpectrum3942.graph fusedMap5108=true := by decide +kernel
theorem certified5108 : Certified (graph core5108) (root 7) 2 4 :=
  of_native_maps core5108 DegreeTwoThreeSpectrum4766.graph DegreeTwoThreeSpectrum3942.graph
    sourceMap5108 fusedMap5108 sourceMap5108_checked fusedMap5108_checked
    DegreeTwoThreeFiniteComparisons.comparison5108
#print axioms sourceMap5108_checked
#print axioms fusedMap5108_checked
#print axioms certified5108
def sourceMap5108swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,2,3,4,5,9,10,11,0,12,13,14,15,6,7,8] (sourceLabel 7 4 2 v)
def fusedMap5108swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 4 2 v)
theorem sourceMap5108swap_checked : acceptsGraphIso
    (source (graph core5108) (root 7) 4 2) DegreeTwoThreeSpectrum4766.graph sourceMap5108swap=true := by decide +kernel
theorem fusedMap5108swap_checked : acceptsGraphIso
    (fused (graph core5108) (root 7) 4 2) DegreeTwoThreeSpectrum3942.graph fusedMap5108swap=true := by decide +kernel
theorem certified5108swap : Certified (graph core5108) (root 7) 4 2 :=
  of_native_maps core5108 DegreeTwoThreeSpectrum4766.graph DegreeTwoThreeSpectrum3942.graph
    sourceMap5108swap fusedMap5108swap sourceMap5108swap_checked fusedMap5108swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5108
#print axioms sourceMap5108swap_checked
#print axioms fusedMap5108swap_checked
#print axioms certified5108swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
