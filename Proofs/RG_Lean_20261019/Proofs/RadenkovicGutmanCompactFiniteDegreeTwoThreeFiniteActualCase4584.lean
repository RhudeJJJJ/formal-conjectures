/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4584 : Family 10 := level10.get ⟨552,by decide⟩
def sourceMap4584 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4584 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4584_checked : acceptsGraphIso
    (source (graph core4584) (root 10) 2 2) DegreeTwoThreeSpectrum7172.graph sourceMap4584=true := by decide +kernel
theorem fusedMap4584_checked : acceptsGraphIso
    (fused (graph core4584) (root 10) 2 2) DegreeTwoThreeSpectrum5206.graph fusedMap4584=true := by decide +kernel
theorem certified4584 : Certified (graph core4584) (root 10) 2 2 :=
  of_native_maps core4584 DegreeTwoThreeSpectrum7172.graph DegreeTwoThreeSpectrum5206.graph
    sourceMap4584 fusedMap4584 sourceMap4584_checked fusedMap4584_checked
    DegreeTwoThreeFiniteComparisons.comparison4584
#print axioms sourceMap4584_checked
#print axioms fusedMap4584_checked
#print axioms certified4584
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
