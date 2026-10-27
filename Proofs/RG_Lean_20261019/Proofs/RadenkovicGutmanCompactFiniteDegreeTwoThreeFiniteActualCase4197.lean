/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4197 : Family 9 := level9.get ⟨33,by decide⟩
def sourceMap4197 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,10,11,12,13,14,15,9,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap4197 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4197_checked : acceptsGraphIso
    (source (graph core4197) (root 9) 2 2) DegreeTwoThreeSpectrum4556.graph sourceMap4197=true := by decide +kernel
theorem fusedMap4197_checked : acceptsGraphIso
    (fused (graph core4197) (root 9) 2 2) DegreeTwoThreeSpectrum3881.graph fusedMap4197=true := by decide +kernel
theorem certified4197 : Certified (graph core4197) (root 9) 2 2 :=
  of_native_maps core4197 DegreeTwoThreeSpectrum4556.graph DegreeTwoThreeSpectrum3881.graph
    sourceMap4197 fusedMap4197 sourceMap4197_checked fusedMap4197_checked
    DegreeTwoThreeFiniteComparisons.comparison4197
#print axioms sourceMap4197_checked
#print axioms fusedMap4197_checked
#print axioms certified4197
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
