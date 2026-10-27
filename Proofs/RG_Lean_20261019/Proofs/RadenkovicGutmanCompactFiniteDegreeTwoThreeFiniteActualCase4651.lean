/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4651 : Family 10 := level10.get ⟨748,by decide⟩
def sourceMap4651 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4651 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4651_checked : acceptsGraphIso
    (source (graph core4651) (root 10) 2 2) DegreeTwoThreeSpectrum7415.graph sourceMap4651=true := by decide +kernel
theorem fusedMap4651_checked : acceptsGraphIso
    (fused (graph core4651) (root 10) 2 2) DegreeTwoThreeSpectrum5510.graph fusedMap4651=true := by decide +kernel
theorem certified4651 : Certified (graph core4651) (root 10) 2 2 :=
  of_native_maps core4651 DegreeTwoThreeSpectrum7415.graph DegreeTwoThreeSpectrum5510.graph
    sourceMap4651 fusedMap4651 sourceMap4651_checked fusedMap4651_checked
    DegreeTwoThreeFiniteComparisons.comparison4651
#print axioms sourceMap4651_checked
#print axioms fusedMap4651_checked
#print axioms certified4651
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
