/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4570 : Family 10 := level10.get ⟨506,by decide⟩
def sourceMap4570 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4570 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4570_checked : acceptsGraphIso
    (source (graph core4570) (root 10) 2 2) DegreeTwoThreeSpectrum7095.graph sourceMap4570=true := by decide +kernel
theorem fusedMap4570_checked : acceptsGraphIso
    (fused (graph core4570) (root 10) 2 2) DegreeTwoThreeSpectrum5143.graph fusedMap4570=true := by decide +kernel
theorem certified4570 : Certified (graph core4570) (root 10) 2 2 :=
  of_native_maps core4570 DegreeTwoThreeSpectrum7095.graph DegreeTwoThreeSpectrum5143.graph
    sourceMap4570 fusedMap4570 sourceMap4570_checked fusedMap4570_checked
    DegreeTwoThreeFiniteComparisons.comparison4570
#print axioms sourceMap4570_checked
#print axioms fusedMap4570_checked
#print axioms certified4570
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
