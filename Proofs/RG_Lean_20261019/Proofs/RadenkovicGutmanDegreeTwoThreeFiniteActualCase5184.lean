/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5184 : Family 8 := level8.get ⟨198,by decide⟩
def sourceMap5184 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5184 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5184_checked : acceptsGraphIso
    (source (graph core5184) (root 8) 2 4) DegreeTwoThreeSpectrum7117.graph sourceMap5184=true := by decide +kernel
theorem fusedMap5184_checked : acceptsGraphIso
    (fused (graph core5184) (root 8) 2 4) DegreeTwoThreeSpectrum5161.graph fusedMap5184=true := by decide +kernel
theorem certified5184 : Certified (graph core5184) (root 8) 2 4 :=
  of_native_maps core5184 DegreeTwoThreeSpectrum7117.graph DegreeTwoThreeSpectrum5161.graph
    sourceMap5184 fusedMap5184 sourceMap5184_checked fusedMap5184_checked
    DegreeTwoThreeFiniteComparisons.comparison5184
#print axioms sourceMap5184_checked
#print axioms fusedMap5184_checked
#print axioms certified5184
def sourceMap5184swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5184swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5184swap_checked : acceptsGraphIso
    (source (graph core5184) (root 8) 4 2) DegreeTwoThreeSpectrum7117.graph sourceMap5184swap=true := by decide +kernel
theorem fusedMap5184swap_checked : acceptsGraphIso
    (fused (graph core5184) (root 8) 4 2) DegreeTwoThreeSpectrum5161.graph fusedMap5184swap=true := by decide +kernel
theorem certified5184swap : Certified (graph core5184) (root 8) 4 2 :=
  of_native_maps core5184 DegreeTwoThreeSpectrum7117.graph DegreeTwoThreeSpectrum5161.graph
    sourceMap5184swap fusedMap5184swap sourceMap5184swap_checked fusedMap5184swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5184
#print axioms sourceMap5184swap_checked
#print axioms fusedMap5184swap_checked
#print axioms certified5184swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
