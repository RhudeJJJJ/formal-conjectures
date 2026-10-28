/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5453 : Family 7 := level7.get ⟨105,by decide⟩
def sourceMap5453 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap5453 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap5453_checked : acceptsGraphIso
    (source (graph core5453) (root 7) 0 0) SmallGeFourSpectrum030.graph sourceMap5453=true := by decide +kernel
theorem fusedMap5453_checked : acceptsGraphIso
    (fused (graph core5453) (root 7) 0 0) DegreeTwoThreeSpectrum148.graph fusedMap5453=true := by decide +kernel
theorem certified5453 : Certified (graph core5453) (root 7) 0 0 :=
  of_native_maps core5453 SmallGeFourSpectrum030.graph DegreeTwoThreeSpectrum148.graph
    sourceMap5453 fusedMap5453 sourceMap5453_checked fusedMap5453_checked
    DegreeTwoThreeFiniteComparisons.comparison5453
#print axioms sourceMap5453_checked
#print axioms fusedMap5453_checked
#print axioms certified5453
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
