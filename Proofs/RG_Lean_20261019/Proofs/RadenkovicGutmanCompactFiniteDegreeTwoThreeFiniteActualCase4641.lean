/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4641 : Family 10 := level10.get ⟨718,by decide⟩
def sourceMap4641 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,15,16,14,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4641 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4641_checked : acceptsGraphIso
    (source (graph core4641) (root 10) 2 2) DegreeTwoThreeSpectrum7376.graph sourceMap4641=true := by decide +kernel
theorem fusedMap4641_checked : acceptsGraphIso
    (fused (graph core4641) (root 10) 2 2) DegreeTwoThreeSpectrum5464.graph fusedMap4641=true := by decide +kernel
theorem certified4641 : Certified (graph core4641) (root 10) 2 2 :=
  of_native_maps core4641 DegreeTwoThreeSpectrum7376.graph DegreeTwoThreeSpectrum5464.graph
    sourceMap4641 fusedMap4641 sourceMap4641_checked fusedMap4641_checked
    DegreeTwoThreeFiniteComparisons.comparison4641
#print axioms sourceMap4641_checked
#print axioms fusedMap4641_checked
#print axioms certified4641
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
