/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4120 : Family 8 := level8.get ⟨89,by decide⟩
def sourceMap4120 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4120 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4120_checked : acceptsGraphIso
    (source (graph core4120) (root 8) 2 2) DegreeTwoThreeSpectrum3618.graph sourceMap4120=true := by decide +kernel
theorem fusedMap4120_checked : acceptsGraphIso
    (fused (graph core4120) (root 8) 2 2) DegreeTwoThreeSpectrum2418.graph fusedMap4120=true := by decide +kernel
theorem certified4120 : Certified (graph core4120) (root 8) 2 2 :=
  of_native_maps core4120 DegreeTwoThreeSpectrum3618.graph DegreeTwoThreeSpectrum2418.graph
    sourceMap4120 fusedMap4120 sourceMap4120_checked fusedMap4120_checked
    DegreeTwoThreeFiniteComparisons.comparison4120
#print axioms sourceMap4120_checked
#print axioms fusedMap4120_checked
#print axioms certified4120
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
