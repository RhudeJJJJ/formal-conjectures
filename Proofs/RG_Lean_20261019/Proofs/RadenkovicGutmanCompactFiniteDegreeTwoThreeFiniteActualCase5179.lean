/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5179 : Family 8 := level8.get ⟨181,by decide⟩
def sourceMap5179 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5179 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5179_checked : acceptsGraphIso
    (source (graph core5179) (root 8) 2 4) DegreeTwoThreeSpectrum7013.graph sourceMap5179=true := by decide +kernel
theorem fusedMap5179_checked : acceptsGraphIso
    (fused (graph core5179) (root 8) 2 4) DegreeTwoThreeSpectrum5830.graph fusedMap5179=true := by decide +kernel
theorem certified5179 : Certified (graph core5179) (root 8) 2 4 :=
  of_native_maps core5179 DegreeTwoThreeSpectrum7013.graph DegreeTwoThreeSpectrum5830.graph
    sourceMap5179 fusedMap5179 sourceMap5179_checked fusedMap5179_checked
    DegreeTwoThreeFiniteComparisons.comparison5179
#print axioms sourceMap5179_checked
#print axioms fusedMap5179_checked
#print axioms certified5179
def sourceMap5179swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5179swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5179swap_checked : acceptsGraphIso
    (source (graph core5179) (root 8) 4 2) DegreeTwoThreeSpectrum7013.graph sourceMap5179swap=true := by decide +kernel
theorem fusedMap5179swap_checked : acceptsGraphIso
    (fused (graph core5179) (root 8) 4 2) DegreeTwoThreeSpectrum5830.graph fusedMap5179swap=true := by decide +kernel
theorem certified5179swap : Certified (graph core5179) (root 8) 4 2 :=
  of_native_maps core5179 DegreeTwoThreeSpectrum7013.graph DegreeTwoThreeSpectrum5830.graph
    sourceMap5179swap fusedMap5179swap sourceMap5179swap_checked fusedMap5179swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5179
#print axioms sourceMap5179swap_checked
#print axioms fusedMap5179swap_checked
#print axioms certified5179swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
