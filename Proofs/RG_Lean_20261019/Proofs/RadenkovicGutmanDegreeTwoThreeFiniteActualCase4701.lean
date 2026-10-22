/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4701 : Family 10 := level10.get ⟨881,by decide⟩
def sourceMap4701 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4701 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4701_checked : acceptsGraphIso
    (source (graph core4701) (root 10) 2 2) DegreeTwoThreeSpectrum7510.graph sourceMap4701=true := by decide +kernel
theorem fusedMap4701_checked : acceptsGraphIso
    (fused (graph core4701) (root 10) 2 2) DegreeTwoThreeSpectrum5732.graph fusedMap4701=true := by decide +kernel
theorem certified4701 : Certified (graph core4701) (root 10) 2 2 :=
  of_native_maps core4701 DegreeTwoThreeSpectrum7510.graph DegreeTwoThreeSpectrum5732.graph
    sourceMap4701 fusedMap4701 sourceMap4701_checked fusedMap4701_checked
    DegreeTwoThreeFiniteComparisons.comparison4701
#print axioms sourceMap4701_checked
#print axioms fusedMap4701_checked
#print axioms certified4701
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
