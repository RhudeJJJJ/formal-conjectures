/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5307 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5307 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,6,7,8,3,4,5,1,0,9,10,11,12,13,14] (sourceLabel 3 2 7 v)
def fusedMap5307 : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 2 7 v)
theorem sourceMap5307_checked : acceptsGraphIso
    (source (graph core5307) (root 3) 2 7) DegreeTwoThreeSpectrum2383.graph sourceMap5307=true := by decide +kernel
theorem fusedMap5307_checked : acceptsGraphIso
    (fused (graph core5307) (root 3) 2 7) DegreeTwoThreeSpectrum2310.graph fusedMap5307=true := by decide +kernel
theorem certified5307 : Certified (graph core5307) (root 3) 2 7 :=
  of_native_maps core5307 DegreeTwoThreeSpectrum2383.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap5307 fusedMap5307 sourceMap5307_checked fusedMap5307_checked
    DegreeTwoThreeFiniteComparisons.comparison5307
#print axioms sourceMap5307_checked
#print axioms fusedMap5307_checked
#print axioms certified5307
def sourceMap5307swap : (Vertices 3 ⊕ Fin 8 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,6,7,8,1,0,9,10,11,12,13,14,3,4,5] (sourceLabel 3 7 2 v)
def fusedMap5307swap : (Vertices 3 ⊕ Fin 11) → Fin 15 :=
  fun v => ![4,5,6,7,3,2,1,0,8,9,10,11,12,13,14] (fusedLabel 3 7 2 v)
theorem sourceMap5307swap_checked : acceptsGraphIso
    (source (graph core5307) (root 3) 7 2) DegreeTwoThreeSpectrum2383.graph sourceMap5307swap=true := by decide +kernel
theorem fusedMap5307swap_checked : acceptsGraphIso
    (fused (graph core5307) (root 3) 7 2) DegreeTwoThreeSpectrum2310.graph fusedMap5307swap=true := by decide +kernel
theorem certified5307swap : Certified (graph core5307) (root 3) 7 2 :=
  of_native_maps core5307 DegreeTwoThreeSpectrum2383.graph DegreeTwoThreeSpectrum2310.graph
    sourceMap5307swap fusedMap5307swap sourceMap5307swap_checked fusedMap5307swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5307
#print axioms sourceMap5307swap_checked
#print axioms fusedMap5307swap_checked
#print axioms certified5307swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
