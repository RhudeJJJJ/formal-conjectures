/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4549 : Family 10 := level10.get ⟨449,by decide⟩
def sourceMap4549 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4549 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4549_checked : acceptsGraphIso
    (source (graph core4549) (root 10) 2 2) DegreeTwoThreeSpectrum6853.graph sourceMap4549=true := by decide +kernel
theorem fusedMap4549_checked : acceptsGraphIso
    (fused (graph core4549) (root 10) 2 2) DegreeTwoThreeSpectrum5873.graph fusedMap4549=true := by decide +kernel
theorem certified4549 : Certified (graph core4549) (root 10) 2 2 :=
  of_native_maps core4549 DegreeTwoThreeSpectrum6853.graph DegreeTwoThreeSpectrum5873.graph
    sourceMap4549 fusedMap4549 sourceMap4549_checked fusedMap4549_checked
    DegreeTwoThreeFiniteComparisons.comparison4549
#print axioms sourceMap4549_checked
#print axioms fusedMap4549_checked
#print axioms certified4549
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
