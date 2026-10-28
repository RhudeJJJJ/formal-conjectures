/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5375 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5375 : (Vertices 4 ⊕ Fin 5 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,11,12,13,14,1,2,3,4,5,6,7,8,9,10] (sourceLabel 4 4 4 v)
def fusedMap5375 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 4 4 v)
theorem sourceMap5375_checked : acceptsGraphIso
    (source (graph core5375) (root 4) 4 4) DegreeTwoThreeSpectrum2996.graph sourceMap5375=true := by decide +kernel
theorem fusedMap5375_checked : acceptsGraphIso
    (fused (graph core5375) (root 4) 4 4) DegreeTwoThreeSpectrum2354.graph fusedMap5375=true := by decide +kernel
theorem certified5375 : Certified (graph core5375) (root 4) 4 4 :=
  of_native_maps core5375 DegreeTwoThreeSpectrum2996.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap5375 fusedMap5375 sourceMap5375_checked fusedMap5375_checked
    DegreeTwoThreeFiniteComparisons.comparison5375
#print axioms sourceMap5375_checked
#print axioms fusedMap5375_checked
#print axioms certified5375
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
