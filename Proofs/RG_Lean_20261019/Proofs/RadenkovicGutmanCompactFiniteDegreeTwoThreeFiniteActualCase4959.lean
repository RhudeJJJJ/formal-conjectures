/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4959 : Family 10 := level10.get ⟨1525,by decide⟩
def sourceMap4959 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4959 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4959_checked : acceptsGraphIso
    (source (graph core4959) (root 10) 2 2) DegreeTwoThreeSpectrum7560.graph sourceMap4959=true := by decide +kernel
theorem fusedMap4959_checked : acceptsGraphIso
    (fused (graph core4959) (root 10) 2 2) DegreeTwoThreeSpectrum5961.graph fusedMap4959=true := by decide +kernel
theorem certified4959 : Certified (graph core4959) (root 10) 2 2 :=
  of_native_maps core4959 DegreeTwoThreeSpectrum7560.graph DegreeTwoThreeSpectrum5961.graph
    sourceMap4959 fusedMap4959 sourceMap4959_checked fusedMap4959_checked
    DegreeTwoThreeFiniteComparisons.comparison4959
#print axioms sourceMap4959_checked
#print axioms fusedMap4959_checked
#print axioms certified4959
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
