/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4136 : Family 8 := level8.get ⟨135,by decide⟩
def sourceMap4136 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4136 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4136_checked : acceptsGraphIso
    (source (graph core4136) (root 8) 2 2) DegreeTwoThreeSpectrum3412.graph sourceMap4136=true := by decide +kernel
theorem fusedMap4136_checked : acceptsGraphIso
    (fused (graph core4136) (root 8) 2 2) DegreeTwoThreeSpectrum2657.graph fusedMap4136=true := by decide +kernel
theorem certified4136 : Certified (graph core4136) (root 8) 2 2 :=
  of_native_maps core4136 DegreeTwoThreeSpectrum3412.graph DegreeTwoThreeSpectrum2657.graph
    sourceMap4136 fusedMap4136 sourceMap4136_checked fusedMap4136_checked
    DegreeTwoThreeFiniteComparisons.comparison4136
#print axioms sourceMap4136_checked
#print axioms fusedMap4136_checked
#print axioms certified4136
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
