/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4556 : Family 10 := level10.get ⟨464,by decide⟩
def sourceMap4556 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4556 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (fusedLabel 10 2 2 v)
theorem sourceMap4556_checked : acceptsGraphIso
    (source (graph core4556) (root 10) 2 2) DegreeTwoThreeSpectrum6802.graph sourceMap4556=true := by decide +kernel
theorem fusedMap4556_checked : acceptsGraphIso
    (fused (graph core4556) (root 10) 2 2) DegreeTwoThreeSpectrum5907.graph fusedMap4556=true := by decide +kernel
theorem certified4556 : Certified (graph core4556) (root 10) 2 2 :=
  of_native_maps core4556 DegreeTwoThreeSpectrum6802.graph DegreeTwoThreeSpectrum5907.graph
    sourceMap4556 fusedMap4556 sourceMap4556_checked fusedMap4556_checked
    DegreeTwoThreeFiniteComparisons.comparison4556
#print axioms sourceMap4556_checked
#print axioms fusedMap4556_checked
#print axioms certified4556
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
