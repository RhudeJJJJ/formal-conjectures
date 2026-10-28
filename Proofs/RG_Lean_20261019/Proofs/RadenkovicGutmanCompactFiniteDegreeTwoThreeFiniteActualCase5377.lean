/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5377 : Family 5 := level5.get ⟨7,by decide⟩
def sourceMap5377 : (Vertices 5 ⊕ Fin 5 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,11,12,13,14,15,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 4 4 v)
def fusedMap5377 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14,15] (fusedLabel 5 4 4 v)
theorem sourceMap5377_checked : acceptsGraphIso
    (source (graph core5377) (root 5) 4 4) DegreeTwoThreeSpectrum4659.graph sourceMap5377=true := by decide +kernel
theorem fusedMap5377_checked : acceptsGraphIso
    (fused (graph core5377) (root 5) 4 4) DegreeTwoThreeSpectrum3856.graph fusedMap5377=true := by decide +kernel
theorem certified5377 : Certified (graph core5377) (root 5) 4 4 :=
  of_native_maps core5377 DegreeTwoThreeSpectrum4659.graph DegreeTwoThreeSpectrum3856.graph
    sourceMap5377 fusedMap5377 sourceMap5377_checked fusedMap5377_checked
    DegreeTwoThreeFiniteComparisons.comparison5377
#print axioms sourceMap5377_checked
#print axioms fusedMap5377_checked
#print axioms certified5377
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
