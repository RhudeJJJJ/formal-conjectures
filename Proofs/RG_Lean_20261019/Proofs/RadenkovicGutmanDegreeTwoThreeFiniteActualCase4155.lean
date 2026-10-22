/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4155 : Family 8 := level8.get ⟨179,by decide⟩
def sourceMap4155 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4155 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4155_checked : acceptsGraphIso
    (source (graph core4155) (root 8) 2 2) DegreeTwoThreeSpectrum3729.graph sourceMap4155=true := by decide +kernel
theorem fusedMap4155_checked : acceptsGraphIso
    (fused (graph core4155) (root 8) 2 2) DegreeTwoThreeSpectrum2943.graph fusedMap4155=true := by decide +kernel
theorem certified4155 : Certified (graph core4155) (root 8) 2 2 :=
  of_native_maps core4155 DegreeTwoThreeSpectrum3729.graph DegreeTwoThreeSpectrum2943.graph
    sourceMap4155 fusedMap4155 sourceMap4155_checked fusedMap4155_checked
    DegreeTwoThreeFiniteComparisons.comparison4155
#print axioms sourceMap4155_checked
#print axioms fusedMap4155_checked
#print axioms certified4155
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
