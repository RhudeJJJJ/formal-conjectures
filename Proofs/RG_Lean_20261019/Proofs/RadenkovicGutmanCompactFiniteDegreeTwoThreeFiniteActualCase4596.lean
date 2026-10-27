/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4596 : Family 10 := level10.get ⟨588,by decide⟩
def sourceMap4596 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4596 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4596_checked : acceptsGraphIso
    (source (graph core4596) (root 10) 2 2) DegreeTwoThreeSpectrum7226.graph sourceMap4596=true := by decide +kernel
theorem fusedMap4596_checked : acceptsGraphIso
    (fused (graph core4596) (root 10) 2 2) DegreeTwoThreeSpectrum5259.graph fusedMap4596=true := by decide +kernel
theorem certified4596 : Certified (graph core4596) (root 10) 2 2 :=
  of_native_maps core4596 DegreeTwoThreeSpectrum7226.graph DegreeTwoThreeSpectrum5259.graph
    sourceMap4596 fusedMap4596 sourceMap4596_checked fusedMap4596_checked
    DegreeTwoThreeFiniteComparisons.comparison4596
#print axioms sourceMap4596_checked
#print axioms fusedMap4596_checked
#print axioms certified4596
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
