/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4724 : Family 10 := level10.get ⟨942,by decide⟩
def sourceMap4724 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4724 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4724_checked : acceptsGraphIso
    (source (graph core4724) (root 10) 2 2) DegreeTwoThreeSpectrum7548.graph sourceMap4724=true := by decide +kernel
theorem fusedMap4724_checked : acceptsGraphIso
    (fused (graph core4724) (root 10) 2 2) DegreeTwoThreeSpectrum5841.graph fusedMap4724=true := by decide +kernel
theorem certified4724 : Certified (graph core4724) (root 10) 2 2 :=
  of_native_maps core4724 DegreeTwoThreeSpectrum7548.graph DegreeTwoThreeSpectrum5841.graph
    sourceMap4724 fusedMap4724 sourceMap4724_checked fusedMap4724_checked
    DegreeTwoThreeFiniteComparisons.comparison4724
#print axioms sourceMap4724_checked
#print axioms fusedMap4724_checked
#print axioms certified4724
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
