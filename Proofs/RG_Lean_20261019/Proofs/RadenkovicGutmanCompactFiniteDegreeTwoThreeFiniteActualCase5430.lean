/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5430 : Family 5 := level5.get ⟨17,by decide⟩
def sourceMap5430 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 5 0 0 v)
def fusedMap5430 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,7,5,6] (fusedLabel 5 0 0 v)
theorem sourceMap5430_checked : acceptsGraphIso
    (source (graph core5430) (root 5) 0 0) SmallGeFourSpectrum004.graph sourceMap5430=true := by decide +kernel
theorem fusedMap5430_checked : acceptsGraphIso
    (fused (graph core5430) (root 5) 0 0) DegreeTwoThreeSpectrum030.graph fusedMap5430=true := by decide +kernel
theorem certified5430 : Certified (graph core5430) (root 5) 0 0 :=
  of_native_maps core5430 SmallGeFourSpectrum004.graph DegreeTwoThreeSpectrum030.graph
    sourceMap5430 fusedMap5430 sourceMap5430_checked fusedMap5430_checked
    DegreeTwoThreeFiniteComparisons.comparison5430
#print axioms sourceMap5430_checked
#print axioms fusedMap5430_checked
#print axioms certified5430
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
