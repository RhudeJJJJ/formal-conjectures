/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5419 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5419 : (Vertices 4 ⊕ Fin 6 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 4 5 5 v)
def fusedMap5419 : (Vertices 4 ⊕ Fin 12) → Fin 17 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15,16] (fusedLabel 4 5 5 v)
theorem sourceMap5419_checked : acceptsGraphIso
    (source (graph core5419) (root 4) 5 5) DegreeTwoThreeSpectrum5956.graph sourceMap5419=true := by decide +kernel
theorem fusedMap5419_checked : acceptsGraphIso
    (fused (graph core5419) (root 4) 5 5) DegreeTwoThreeSpectrum4961.graph fusedMap5419=true := by decide +kernel
theorem certified5419 : Certified (graph core5419) (root 4) 5 5 :=
  of_native_maps core5419 DegreeTwoThreeSpectrum5956.graph DegreeTwoThreeSpectrum4961.graph
    sourceMap5419 fusedMap5419 sourceMap5419_checked fusedMap5419_checked
    DegreeTwoThreeFiniteComparisons.comparison5419
#print axioms sourceMap5419_checked
#print axioms fusedMap5419_checked
#print axioms certified5419
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
