/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4173 : Family 8 := level8.get ⟨219,by decide⟩
def sourceMap4173 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,12,13,14,6,7,8,9,10,11] (sourceLabel 8 2 2 v)
def fusedMap4173 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4173_checked : acceptsGraphIso
    (source (graph core4173) (root 8) 2 2) DegreeTwoThreeSpectrum3810.graph sourceMap4173=true := by decide +kernel
theorem fusedMap4173_checked : acceptsGraphIso
    (fused (graph core4173) (root 8) 2 2) DegreeTwoThreeSpectrum2533.graph fusedMap4173=true := by decide +kernel
theorem certified4173 : Certified (graph core4173) (root 8) 2 2 :=
  of_native_maps core4173 DegreeTwoThreeSpectrum3810.graph DegreeTwoThreeSpectrum2533.graph
    sourceMap4173 fusedMap4173 sourceMap4173_checked fusedMap4173_checked
    DegreeTwoThreeFiniteComparisons.comparison4173
#print axioms sourceMap4173_checked
#print axioms fusedMap4173_checked
#print axioms certified4173
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
