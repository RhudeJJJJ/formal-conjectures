/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5155 : Family 8 := level8.get ⟨126,by decide⟩
def sourceMap5155 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5155 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5155_checked : acceptsGraphIso
    (source (graph core5155) (root 8) 2 4) DegreeTwoThreeSpectrum6404.graph sourceMap5155=true := by decide +kernel
theorem fusedMap5155_checked : acceptsGraphIso
    (fused (graph core5155) (root 8) 2 4) DegreeTwoThreeSpectrum5343.graph fusedMap5155=true := by decide +kernel
theorem certified5155 : Certified (graph core5155) (root 8) 2 4 :=
  of_native_maps core5155 DegreeTwoThreeSpectrum6404.graph DegreeTwoThreeSpectrum5343.graph
    sourceMap5155 fusedMap5155 sourceMap5155_checked fusedMap5155_checked
    DegreeTwoThreeFiniteComparisons.comparison5155
#print axioms sourceMap5155_checked
#print axioms fusedMap5155_checked
#print axioms certified5155
def sourceMap5155swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5155swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5155swap_checked : acceptsGraphIso
    (source (graph core5155) (root 8) 4 2) DegreeTwoThreeSpectrum6404.graph sourceMap5155swap=true := by decide +kernel
theorem fusedMap5155swap_checked : acceptsGraphIso
    (fused (graph core5155) (root 8) 4 2) DegreeTwoThreeSpectrum5343.graph fusedMap5155swap=true := by decide +kernel
theorem certified5155swap : Certified (graph core5155) (root 8) 4 2 :=
  of_native_maps core5155 DegreeTwoThreeSpectrum6404.graph DegreeTwoThreeSpectrum5343.graph
    sourceMap5155swap fusedMap5155swap sourceMap5155swap_checked fusedMap5155swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5155
#print axioms sourceMap5155swap_checked
#print axioms fusedMap5155swap_checked
#print axioms certified5155swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
