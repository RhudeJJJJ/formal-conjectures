/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5435 : Family 6 := level6.get ⟨40,by decide⟩
def sourceMap5435 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,5,6,7,8,1,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap5435 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,7,8,5,6] (fusedLabel 6 0 0 v)
theorem sourceMap5435_checked : acceptsGraphIso
    (source (graph core5435) (root 6) 0 0) DegreeTwoThreeSpectrum058.graph sourceMap5435=true := by decide +kernel
theorem fusedMap5435_checked : acceptsGraphIso
    (fused (graph core5435) (root 6) 0 0) DegreeTwoThreeSpectrum064.graph fusedMap5435=true := by decide +kernel
theorem certified5435 : Certified (graph core5435) (root 6) 0 0 :=
  of_native_maps core5435 DegreeTwoThreeSpectrum058.graph DegreeTwoThreeSpectrum064.graph
    sourceMap5435 fusedMap5435 sourceMap5435_checked fusedMap5435_checked
    DegreeTwoThreeFiniteComparisons.comparison5435
#print axioms sourceMap5435_checked
#print axioms fusedMap5435_checked
#print axioms certified5435
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
