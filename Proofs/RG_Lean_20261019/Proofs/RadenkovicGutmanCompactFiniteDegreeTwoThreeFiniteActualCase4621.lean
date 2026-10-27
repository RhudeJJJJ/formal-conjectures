/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4621 : Family 10 := level10.get ⟨663,by decide⟩
def sourceMap4621 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,14,15,16,13,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4621 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4621_checked : acceptsGraphIso
    (source (graph core4621) (root 10) 2 2) DegreeTwoThreeSpectrum7319.graph sourceMap4621=true := by decide +kernel
theorem fusedMap4621_checked : acceptsGraphIso
    (fused (graph core4621) (root 10) 2 2) DegreeTwoThreeSpectrum5372.graph fusedMap4621=true := by decide +kernel
theorem certified4621 : Certified (graph core4621) (root 10) 2 2 :=
  of_native_maps core4621 DegreeTwoThreeSpectrum7319.graph DegreeTwoThreeSpectrum5372.graph
    sourceMap4621 fusedMap4621 sourceMap4621_checked fusedMap4621_checked
    DegreeTwoThreeFiniteComparisons.comparison4621
#print axioms sourceMap4621_checked
#print axioms fusedMap4621_checked
#print axioms certified4621
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
