/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4060 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap4060 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,9,10,11,12,13,8,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap4060 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,13,7,8,9,10,11,12] (fusedLabel 7 2 2 v)
theorem sourceMap4060_checked : acceptsGraphIso
    (source (graph core4060) (root 7) 2 2) DegreeTwoThreeSpectrum1859.graph sourceMap4060=true := by decide +kernel
theorem fusedMap4060_checked : acceptsGraphIso
    (fused (graph core4060) (root 7) 2 2) DegreeTwoThreeSpectrum1738.graph fusedMap4060=true := by decide +kernel
theorem certified4060 : Certified (graph core4060) (root 7) 2 2 :=
  of_native_maps core4060 DegreeTwoThreeSpectrum1859.graph DegreeTwoThreeSpectrum1738.graph
    sourceMap4060 fusedMap4060 sourceMap4060_checked fusedMap4060_checked
    DegreeTwoThreeFiniteComparisons.comparison4060
#print axioms sourceMap4060_checked
#print axioms fusedMap4060_checked
#print axioms certified4060
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
