/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4897 : Family 10 := level10.get ⟨1364,by decide⟩
def sourceMap4897 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4897 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4897_checked : acceptsGraphIso
    (source (graph core4897) (root 10) 2 2) DegreeTwoThreeSpectrum7443.graph sourceMap4897=true := by decide +kernel
theorem fusedMap4897_checked : acceptsGraphIso
    (fused (graph core4897) (root 10) 2 2) DegreeTwoThreeSpectrum6702.graph fusedMap4897=true := by decide +kernel
theorem certified4897 : Certified (graph core4897) (root 10) 2 2 :=
  of_native_maps core4897 DegreeTwoThreeSpectrum7443.graph DegreeTwoThreeSpectrum6702.graph
    sourceMap4897 fusedMap4897 sourceMap4897_checked fusedMap4897_checked
    DegreeTwoThreeFiniteComparisons.comparison4897
#print axioms sourceMap4897_checked
#print axioms fusedMap4897_checked
#print axioms certified4897
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
