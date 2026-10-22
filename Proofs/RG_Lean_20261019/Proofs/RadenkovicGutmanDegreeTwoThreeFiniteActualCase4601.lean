/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4601 : Family 10 := level10.get ⟨606,by decide⟩
def sourceMap4601 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4601 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4601_checked : acceptsGraphIso
    (source (graph core4601) (root 10) 2 2) DegreeTwoThreeSpectrum7255.graph sourceMap4601=true := by decide +kernel
theorem fusedMap4601_checked : acceptsGraphIso
    (fused (graph core4601) (root 10) 2 2) DegreeTwoThreeSpectrum5285.graph fusedMap4601=true := by decide +kernel
theorem certified4601 : Certified (graph core4601) (root 10) 2 2 :=
  of_native_maps core4601 DegreeTwoThreeSpectrum7255.graph DegreeTwoThreeSpectrum5285.graph
    sourceMap4601 fusedMap4601 sourceMap4601_checked fusedMap4601_checked
    DegreeTwoThreeFiniteComparisons.comparison4601
#print axioms sourceMap4601_checked
#print axioms fusedMap4601_checked
#print axioms certified4601
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
