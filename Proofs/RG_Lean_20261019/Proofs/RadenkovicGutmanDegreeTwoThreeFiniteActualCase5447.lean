/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5447 : Family 7 := level7.get ⟨89,by decide⟩
def sourceMap5447 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap5447 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,3,4,1,2] (fusedLabel 7 0 0 v)
theorem sourceMap5447_checked : acceptsGraphIso
    (source (graph core5447) (root 7) 0 0) DegreeTwoThreeSpectrum144.graph sourceMap5447=true := by decide +kernel
theorem fusedMap5447_checked : acceptsGraphIso
    (fused (graph core5447) (root 7) 0 0) DegreeTwoThreeSpectrum130.graph fusedMap5447=true := by decide +kernel
theorem certified5447 : Certified (graph core5447) (root 7) 0 0 :=
  of_native_maps core5447 DegreeTwoThreeSpectrum144.graph DegreeTwoThreeSpectrum130.graph
    sourceMap5447 fusedMap5447 sourceMap5447_checked fusedMap5447_checked
    DegreeTwoThreeFiniteComparisons.comparison5447
#print axioms sourceMap5447_checked
#print axioms fusedMap5447_checked
#print axioms certified5447
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
