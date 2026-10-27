/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4721 : Family 10 := level10.get ⟨934,by decide⟩
def sourceMap4721 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4721 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4721_checked : acceptsGraphIso
    (source (graph core4721) (root 10) 2 2) DegreeTwoThreeSpectrum7546.graph sourceMap4721=true := by decide +kernel
theorem fusedMap4721_checked : acceptsGraphIso
    (fused (graph core4721) (root 10) 2 2) DegreeTwoThreeSpectrum5829.graph fusedMap4721=true := by decide +kernel
theorem certified4721 : Certified (graph core4721) (root 10) 2 2 :=
  of_native_maps core4721 DegreeTwoThreeSpectrum7546.graph DegreeTwoThreeSpectrum5829.graph
    sourceMap4721 fusedMap4721 sourceMap4721_checked fusedMap4721_checked
    DegreeTwoThreeFiniteComparisons.comparison4721
#print axioms sourceMap4721_checked
#print axioms fusedMap4721_checked
#print axioms certified4721
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
