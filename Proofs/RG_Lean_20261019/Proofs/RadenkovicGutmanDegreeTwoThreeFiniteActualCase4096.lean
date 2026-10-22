/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4096 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap4096 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (sourceLabel 7 2 2 v)
def fusedMap4096 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4096_checked : acceptsGraphIso
    (source (graph core4096) (root 7) 2 2) DegreeTwoThreeSpectrum2308.graph sourceMap4096=true := by decide +kernel
theorem fusedMap4096_checked : acceptsGraphIso
    (fused (graph core4096) (root 7) 2 2) DegreeTwoThreeSpectrum1950.graph fusedMap4096=true := by decide +kernel
theorem certified4096 : Certified (graph core4096) (root 7) 2 2 :=
  of_native_maps core4096 DegreeTwoThreeSpectrum2308.graph DegreeTwoThreeSpectrum1950.graph
    sourceMap4096 fusedMap4096 sourceMap4096_checked fusedMap4096_checked
    DegreeTwoThreeFiniteComparisons.comparison4096
#print axioms sourceMap4096_checked
#print axioms fusedMap4096_checked
#print axioms certified4096
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
