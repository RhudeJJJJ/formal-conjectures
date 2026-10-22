/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4191 : Family 8 := level8.get ⟨268,by decide⟩
def sourceMap4191 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,7,8,9,10,11,12,13,14,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4191 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4191_checked : acceptsGraphIso
    (source (graph core4191) (root 8) 2 2) DegreeTwoThreeSpectrum3852.graph sourceMap4191=true := by decide +kernel
theorem fusedMap4191_checked : acceptsGraphIso
    (fused (graph core4191) (root 8) 2 2) DegreeTwoThreeSpectrum3022.graph fusedMap4191=true := by decide +kernel
theorem certified4191 : Certified (graph core4191) (root 8) 2 2 :=
  of_native_maps core4191 DegreeTwoThreeSpectrum3852.graph DegreeTwoThreeSpectrum3022.graph
    sourceMap4191 fusedMap4191 sourceMap4191_checked fusedMap4191_checked
    DegreeTwoThreeFiniteComparisons.comparison4191
#print axioms sourceMap4191_checked
#print axioms fusedMap4191_checked
#print axioms certified4191
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
