/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5427 : Family 4 := level4.get ⟨7,by decide⟩
def sourceMap5427 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,5,6,1,2,3,4] (sourceLabel 4 0 0 v)
def fusedMap5427 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,5,6,3,4] (fusedLabel 4 0 0 v)
theorem sourceMap5427_checked : acceptsGraphIso
    (source (graph core5427) (root 4) 0 0) SmallGeFourSpectrum000.graph sourceMap5427=true := by decide +kernel
theorem fusedMap5427_checked : acceptsGraphIso
    (fused (graph core5427) (root 4) 0 0) DegreeTwoThreeSpectrum013.graph fusedMap5427=true := by decide +kernel
theorem certified5427 : Certified (graph core5427) (root 4) 0 0 :=
  of_native_maps core5427 SmallGeFourSpectrum000.graph DegreeTwoThreeSpectrum013.graph
    sourceMap5427 fusedMap5427 sourceMap5427_checked fusedMap5427_checked
    DegreeTwoThreeFiniteComparisons.comparison5427
#print axioms sourceMap5427_checked
#print axioms fusedMap5427_checked
#print axioms certified5427
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
