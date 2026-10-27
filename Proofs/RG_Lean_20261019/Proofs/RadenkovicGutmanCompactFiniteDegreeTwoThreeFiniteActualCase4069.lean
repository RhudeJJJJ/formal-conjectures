/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4069 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap4069 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![5,0,1,2,3,4,12,13,6,7,8,9,10,11] (sourceLabel 7 2 2 v)
def fusedMap4069 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4069_checked : acceptsGraphIso
    (source (graph core4069) (root 7) 2 2) DegreeTwoThreeSpectrum2067.graph sourceMap4069=true := by decide +kernel
theorem fusedMap4069_checked : acceptsGraphIso
    (fused (graph core4069) (root 7) 2 2) DegreeTwoThreeSpectrum1790.graph fusedMap4069=true := by decide +kernel
theorem certified4069 : Certified (graph core4069) (root 7) 2 2 :=
  of_native_maps core4069 DegreeTwoThreeSpectrum2067.graph DegreeTwoThreeSpectrum1790.graph
    sourceMap4069 fusedMap4069 sourceMap4069_checked fusedMap4069_checked
    DegreeTwoThreeFiniteComparisons.comparison4069
#print axioms sourceMap4069_checked
#print axioms fusedMap4069_checked
#print axioms certified4069
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
