/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4955 : Family 10 := level10.get ⟨1498,by decide⟩
def sourceMap4955 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4955 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4955_checked : acceptsGraphIso
    (source (graph core4955) (root 10) 2 2) DegreeTwoThreeSpectrum7217.graph sourceMap4955=true := by decide +kernel
theorem fusedMap4955_checked : acceptsGraphIso
    (fused (graph core4955) (root 10) 2 2) DegreeTwoThreeSpectrum7003.graph fusedMap4955=true := by decide +kernel
theorem certified4955 : Certified (graph core4955) (root 10) 2 2 :=
  of_native_maps core4955 DegreeTwoThreeSpectrum7217.graph DegreeTwoThreeSpectrum7003.graph
    sourceMap4955 fusedMap4955 sourceMap4955_checked fusedMap4955_checked
    DegreeTwoThreeFiniteComparisons.comparison4955
#print axioms sourceMap4955_checked
#print axioms fusedMap4955_checked
#print axioms certified4955
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
