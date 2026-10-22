/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4638 : Family 10 := level10.get ⟨710,by decide⟩
def sourceMap4638 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4638 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4638_checked : acceptsGraphIso
    (source (graph core4638) (root 10) 2 2) DegreeTwoThreeSpectrum7369.graph sourceMap4638=true := by decide +kernel
theorem fusedMap4638_checked : acceptsGraphIso
    (fused (graph core4638) (root 10) 2 2) DegreeTwoThreeSpectrum5452.graph fusedMap4638=true := by decide +kernel
theorem certified4638 : Certified (graph core4638) (root 10) 2 2 :=
  of_native_maps core4638 DegreeTwoThreeSpectrum7369.graph DegreeTwoThreeSpectrum5452.graph
    sourceMap4638 fusedMap4638 sourceMap4638_checked fusedMap4638_checked
    DegreeTwoThreeFiniteComparisons.comparison4638
#print axioms sourceMap4638_checked
#print axioms fusedMap4638_checked
#print axioms certified4638
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
