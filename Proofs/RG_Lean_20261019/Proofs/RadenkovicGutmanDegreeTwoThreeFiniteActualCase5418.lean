/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5418 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5418 : (Vertices 3 ⊕ Fin 6 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,13,14,15,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 3 5 5 v)
def fusedMap5418 : (Vertices 3 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 3 5 5 v)
theorem sourceMap5418_checked : acceptsGraphIso
    (source (graph core5418) (root 3) 5 5) DegreeTwoThreeSpectrum4170.graph sourceMap5418=true := by decide +kernel
theorem fusedMap5418_checked : acceptsGraphIso
    (fused (graph core5418) (root 3) 5 5) DegreeTwoThreeSpectrum3869.graph fusedMap5418=true := by decide +kernel
theorem certified5418 : Certified (graph core5418) (root 3) 5 5 :=
  of_native_maps core5418 DegreeTwoThreeSpectrum4170.graph DegreeTwoThreeSpectrum3869.graph
    sourceMap5418 fusedMap5418 sourceMap5418_checked fusedMap5418_checked
    DegreeTwoThreeFiniteComparisons.comparison5418
#print axioms sourceMap5418_checked
#print axioms fusedMap5418_checked
#print axioms certified5418
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
