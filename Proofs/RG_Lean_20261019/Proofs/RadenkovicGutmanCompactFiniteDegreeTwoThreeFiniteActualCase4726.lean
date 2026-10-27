/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4726 : Family 10 := level10.get ⟨946,by decide⟩
def sourceMap4726 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4726 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4726_checked : acceptsGraphIso
    (source (graph core4726) (root 10) 2 2) DegreeTwoThreeSpectrum7515.graph sourceMap4726=true := by decide +kernel
theorem fusedMap4726_checked : acceptsGraphIso
    (fused (graph core4726) (root 10) 2 2) DegreeTwoThreeSpectrum5845.graph fusedMap4726=true := by decide +kernel
theorem certified4726 : Certified (graph core4726) (root 10) 2 2 :=
  of_native_maps core4726 DegreeTwoThreeSpectrum7515.graph DegreeTwoThreeSpectrum5845.graph
    sourceMap4726 fusedMap4726 sourceMap4726_checked fusedMap4726_checked
    DegreeTwoThreeFiniteComparisons.comparison4726
#print axioms sourceMap4726_checked
#print axioms fusedMap4726_checked
#print axioms certified4726
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
