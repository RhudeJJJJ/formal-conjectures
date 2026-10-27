/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4605 : Family 10 := level10.get ⟨612,by decide⟩
def sourceMap4605 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4605 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4605_checked : acceptsGraphIso
    (source (graph core4605) (root 10) 2 2) DegreeTwoThreeSpectrum7253.graph sourceMap4605=true := by decide +kernel
theorem fusedMap4605_checked : acceptsGraphIso
    (fused (graph core4605) (root 10) 2 2) DegreeTwoThreeSpectrum5295.graph fusedMap4605=true := by decide +kernel
theorem certified4605 : Certified (graph core4605) (root 10) 2 2 :=
  of_native_maps core4605 DegreeTwoThreeSpectrum7253.graph DegreeTwoThreeSpectrum5295.graph
    sourceMap4605 fusedMap4605 sourceMap4605_checked fusedMap4605_checked
    DegreeTwoThreeFiniteComparisons.comparison4605
#print axioms sourceMap4605_checked
#print axioms fusedMap4605_checked
#print axioms certified4605
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
