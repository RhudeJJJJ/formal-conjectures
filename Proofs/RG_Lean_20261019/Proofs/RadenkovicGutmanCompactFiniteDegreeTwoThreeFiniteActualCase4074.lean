/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4074 : Family 7 := level7.get ⟨53,by decide⟩
def sourceMap4074 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,7,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap4074 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4074_checked : acceptsGraphIso
    (source (graph core4074) (root 7) 2 2) DegreeTwoThreeSpectrum2183.graph sourceMap4074=true := by decide +kernel
theorem fusedMap4074_checked : acceptsGraphIso
    (fused (graph core4074) (root 7) 2 2) DegreeTwoThreeSpectrum1873.graph fusedMap4074=true := by decide +kernel
theorem certified4074 : Certified (graph core4074) (root 7) 2 2 :=
  of_native_maps core4074 DegreeTwoThreeSpectrum2183.graph DegreeTwoThreeSpectrum1873.graph
    sourceMap4074 fusedMap4074 sourceMap4074_checked fusedMap4074_checked
    DegreeTwoThreeFiniteComparisons.comparison4074
#print axioms sourceMap4074_checked
#print axioms fusedMap4074_checked
#print axioms certified4074
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
