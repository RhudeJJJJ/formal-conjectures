/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4066 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap4066 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4066 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4066_checked : acceptsGraphIso
    (source (graph core4066) (root 7) 2 2) DegreeTwoThreeSpectrum1981.graph sourceMap4066=true := by decide +kernel
theorem fusedMap4066_checked : acceptsGraphIso
    (fused (graph core4066) (root 7) 2 2) DegreeTwoThreeSpectrum1753.graph fusedMap4066=true := by decide +kernel
theorem certified4066 : Certified (graph core4066) (root 7) 2 2 :=
  of_native_maps core4066 DegreeTwoThreeSpectrum1981.graph DegreeTwoThreeSpectrum1753.graph
    sourceMap4066 fusedMap4066 sourceMap4066_checked fusedMap4066_checked
    DegreeTwoThreeFiniteComparisons.comparison4066
#print axioms sourceMap4066_checked
#print axioms fusedMap4066_checked
#print axioms certified4066
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
