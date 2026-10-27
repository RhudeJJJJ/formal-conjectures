/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4075 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap4075 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,8,9,10,11,12,13,7,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap4075 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4075_checked : acceptsGraphIso
    (source (graph core4075) (root 7) 2 2) DegreeTwoThreeSpectrum2184.graph sourceMap4075=true := by decide +kernel
theorem fusedMap4075_checked : acceptsGraphIso
    (fused (graph core4075) (root 7) 2 2) DegreeTwoThreeSpectrum1882.graph fusedMap4075=true := by decide +kernel
theorem certified4075 : Certified (graph core4075) (root 7) 2 2 :=
  of_native_maps core4075 DegreeTwoThreeSpectrum2184.graph DegreeTwoThreeSpectrum1882.graph
    sourceMap4075 fusedMap4075 sourceMap4075_checked fusedMap4075_checked
    DegreeTwoThreeFiniteComparisons.comparison4075
#print axioms sourceMap4075_checked
#print axioms fusedMap4075_checked
#print axioms certified4075
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
