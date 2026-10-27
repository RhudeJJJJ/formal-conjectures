/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4067 : Family 7 := level7.get ⟨33,by decide⟩
def sourceMap4067 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4067 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4067_checked : acceptsGraphIso
    (source (graph core4067) (root 7) 2 2) DegreeTwoThreeSpectrum2031.graph sourceMap4067=true := by decide +kernel
theorem fusedMap4067_checked : acceptsGraphIso
    (fused (graph core4067) (root 7) 2 2) DegreeTwoThreeSpectrum1771.graph fusedMap4067=true := by decide +kernel
theorem certified4067 : Certified (graph core4067) (root 7) 2 2 :=
  of_native_maps core4067 DegreeTwoThreeSpectrum2031.graph DegreeTwoThreeSpectrum1771.graph
    sourceMap4067 fusedMap4067 sourceMap4067_checked fusedMap4067_checked
    DegreeTwoThreeFiniteComparisons.comparison4067
#print axioms sourceMap4067_checked
#print axioms fusedMap4067_checked
#print axioms certified4067
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
