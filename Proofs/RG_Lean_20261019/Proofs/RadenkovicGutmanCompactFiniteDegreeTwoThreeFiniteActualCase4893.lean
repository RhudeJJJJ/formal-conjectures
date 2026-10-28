/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons97
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4893 : Family 10 := level10.get ⟨1357,by decide⟩
def sourceMap4893 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4893 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4893_checked : acceptsGraphIso
    (source (graph core4893) (root 10) 2 2) DegreeTwoThreeSpectrum7438.graph sourceMap4893=true := by decide +kernel
theorem fusedMap4893_checked : acceptsGraphIso
    (fused (graph core4893) (root 10) 2 2) DegreeTwoThreeSpectrum6692.graph fusedMap4893=true := by decide +kernel
theorem certified4893 : Certified (graph core4893) (root 10) 2 2 :=
  of_native_maps core4893 DegreeTwoThreeSpectrum7438.graph DegreeTwoThreeSpectrum6692.graph
    sourceMap4893 fusedMap4893 sourceMap4893_checked fusedMap4893_checked
    DegreeTwoThreeFiniteComparisons.comparison4893
#print axioms sourceMap4893_checked
#print axioms fusedMap4893_checked
#print axioms certified4893
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
