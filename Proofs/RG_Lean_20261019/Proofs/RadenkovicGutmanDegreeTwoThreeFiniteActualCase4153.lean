/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4153 : Family 8 := level8.get ⟨175,by decide⟩
def sourceMap4153 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 8 2 2 v)
def fusedMap4153 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4153_checked : acceptsGraphIso
    (source (graph core4153) (root 8) 2 2) DegreeTwoThreeSpectrum3610.graph sourceMap4153=true := by decide +kernel
theorem fusedMap4153_checked : acceptsGraphIso
    (fused (graph core4153) (root 8) 2 2) DegreeTwoThreeSpectrum2913.graph fusedMap4153=true := by decide +kernel
theorem certified4153 : Certified (graph core4153) (root 8) 2 2 :=
  of_native_maps core4153 DegreeTwoThreeSpectrum3610.graph DegreeTwoThreeSpectrum2913.graph
    sourceMap4153 fusedMap4153 sourceMap4153_checked fusedMap4153_checked
    DegreeTwoThreeFiniteComparisons.comparison4153
#print axioms sourceMap4153_checked
#print axioms fusedMap4153_checked
#print axioms certified4153
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
