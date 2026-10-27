/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4114 : Family 8 := level8.get ⟨74,by decide⟩
def sourceMap4114 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4114 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4114_checked : acceptsGraphIso
    (source (graph core4114) (root 8) 2 2) DegreeTwoThreeSpectrum3624.graph sourceMap4114=true := by decide +kernel
theorem fusedMap4114_checked : acceptsGraphIso
    (fused (graph core4114) (root 8) 2 2) DegreeTwoThreeSpectrum2385.graph fusedMap4114=true := by decide +kernel
theorem certified4114 : Certified (graph core4114) (root 8) 2 2 :=
  of_native_maps core4114 DegreeTwoThreeSpectrum3624.graph DegreeTwoThreeSpectrum2385.graph
    sourceMap4114 fusedMap4114 sourceMap4114_checked fusedMap4114_checked
    DegreeTwoThreeFiniteComparisons.comparison4114
#print axioms sourceMap4114_checked
#print axioms fusedMap4114_checked
#print axioms certified4114
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
