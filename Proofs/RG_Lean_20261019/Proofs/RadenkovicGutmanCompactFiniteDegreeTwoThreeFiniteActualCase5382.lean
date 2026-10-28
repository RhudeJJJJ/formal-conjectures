/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5382 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap5382 : (Vertices 6 ⊕ Fin 5 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,16,6,7,8,9,10,11,12,13,14,15] (sourceLabel 6 4 4 v)
def fusedMap5382 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15,16] (fusedLabel 6 4 4 v)
theorem sourceMap5382_checked : acceptsGraphIso
    (source (graph core5382) (root 6) 4 4) DegreeTwoThreeSpectrum7041.graph sourceMap5382=true := by decide +kernel
theorem fusedMap5382_checked : acceptsGraphIso
    (fused (graph core5382) (root 6) 4 4) DegreeTwoThreeSpectrum4963.graph fusedMap5382=true := by decide +kernel
theorem certified5382 : Certified (graph core5382) (root 6) 4 4 :=
  of_native_maps core5382 DegreeTwoThreeSpectrum7041.graph DegreeTwoThreeSpectrum4963.graph
    sourceMap5382 fusedMap5382 sourceMap5382_checked fusedMap5382_checked
    DegreeTwoThreeFiniteComparisons.comparison5382
#print axioms sourceMap5382_checked
#print axioms fusedMap5382_checked
#print axioms certified5382
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
