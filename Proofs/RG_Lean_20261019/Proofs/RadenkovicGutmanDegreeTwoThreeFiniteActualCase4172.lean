/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4172 : Family 8 := level8.get ⟨218,by decide⟩
def sourceMap4172 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4172 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4172_checked : acceptsGraphIso
    (source (graph core4172) (root 8) 2 2) DegreeTwoThreeSpectrum3809.graph sourceMap4172=true := by decide +kernel
theorem fusedMap4172_checked : acceptsGraphIso
    (fused (graph core4172) (root 8) 2 2) DegreeTwoThreeSpectrum2532.graph fusedMap4172=true := by decide +kernel
theorem certified4172 : Certified (graph core4172) (root 8) 2 2 :=
  of_native_maps core4172 DegreeTwoThreeSpectrum3809.graph DegreeTwoThreeSpectrum2532.graph
    sourceMap4172 fusedMap4172 sourceMap4172_checked fusedMap4172_checked
    DegreeTwoThreeFiniteComparisons.comparison4172
#print axioms sourceMap4172_checked
#print axioms fusedMap4172_checked
#print axioms certified4172
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
