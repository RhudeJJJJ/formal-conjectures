/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4702 : Family 10 := level10.get ⟨886,by decide⟩
def sourceMap4702 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4702 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4702_checked : acceptsGraphIso
    (source (graph core4702) (root 10) 2 2) DegreeTwoThreeSpectrum7538.graph sourceMap4702=true := by decide +kernel
theorem fusedMap4702_checked : acceptsGraphIso
    (fused (graph core4702) (root 10) 2 2) DegreeTwoThreeSpectrum5740.graph fusedMap4702=true := by decide +kernel
theorem certified4702 : Certified (graph core4702) (root 10) 2 2 :=
  of_native_maps core4702 DegreeTwoThreeSpectrum7538.graph DegreeTwoThreeSpectrum5740.graph
    sourceMap4702 fusedMap4702 sourceMap4702_checked fusedMap4702_checked
    DegreeTwoThreeFiniteComparisons.comparison4702
#print axioms sourceMap4702_checked
#print axioms fusedMap4702_checked
#print axioms certified4702
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
