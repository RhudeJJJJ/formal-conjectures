/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4061 : Family 7 := level7.get ⟨11,by decide⟩
def sourceMap4061 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![6,0,1,2,3,4,5,13,7,8,9,10,11,12] (sourceLabel 7 2 2 v)
def fusedMap4061 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4061_checked : acceptsGraphIso
    (source (graph core4061) (root 7) 2 2) DegreeTwoThreeSpectrum2068.graph sourceMap4061=true := by decide +kernel
theorem fusedMap4061_checked : acceptsGraphIso
    (fused (graph core4061) (root 7) 2 2) DegreeTwoThreeSpectrum1713.graph fusedMap4061=true := by decide +kernel
theorem certified4061 : Certified (graph core4061) (root 7) 2 2 :=
  of_native_maps core4061 DegreeTwoThreeSpectrum2068.graph DegreeTwoThreeSpectrum1713.graph
    sourceMap4061 fusedMap4061 sourceMap4061_checked fusedMap4061_checked
    DegreeTwoThreeFiniteComparisons.comparison4061
#print axioms sourceMap4061_checked
#print axioms fusedMap4061_checked
#print axioms certified4061
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
