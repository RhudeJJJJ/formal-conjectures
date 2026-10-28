/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5437 : Family 6 := level6.get ⟨44,by decide⟩
def sourceMap5437 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap5437 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap5437_checked : acceptsGraphIso
    (source (graph core5437) (root 6) 0 0) SmallGeFourSpectrum012.graph sourceMap5437=true := by decide +kernel
theorem fusedMap5437_checked : acceptsGraphIso
    (fused (graph core5437) (root 6) 0 0) DegreeTwoThreeSpectrum069.graph fusedMap5437=true := by decide +kernel
theorem certified5437 : Certified (graph core5437) (root 6) 0 0 :=
  of_native_maps core5437 SmallGeFourSpectrum012.graph DegreeTwoThreeSpectrum069.graph
    sourceMap5437 fusedMap5437 sourceMap5437_checked fusedMap5437_checked
    DegreeTwoThreeFiniteComparisons.comparison5437
#print axioms sourceMap5437_checked
#print axioms fusedMap5437_checked
#print axioms certified5437
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
