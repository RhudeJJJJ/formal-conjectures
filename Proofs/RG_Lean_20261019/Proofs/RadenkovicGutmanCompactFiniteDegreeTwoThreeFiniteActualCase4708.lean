/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4708 : Family 10 := level10.get ⟨902,by decide⟩
def sourceMap4708 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4708 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4708_checked : acceptsGraphIso
    (source (graph core4708) (root 10) 2 2) DegreeTwoThreeSpectrum7541.graph sourceMap4708=true := by decide +kernel
theorem fusedMap4708_checked : acceptsGraphIso
    (fused (graph core4708) (root 10) 2 2) DegreeTwoThreeSpectrum5768.graph fusedMap4708=true := by decide +kernel
theorem certified4708 : Certified (graph core4708) (root 10) 2 2 :=
  of_native_maps core4708 DegreeTwoThreeSpectrum7541.graph DegreeTwoThreeSpectrum5768.graph
    sourceMap4708 fusedMap4708 sourceMap4708_checked fusedMap4708_checked
    DegreeTwoThreeFiniteComparisons.comparison4708
#print axioms sourceMap4708_checked
#print axioms fusedMap4708_checked
#print axioms certified4708
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
