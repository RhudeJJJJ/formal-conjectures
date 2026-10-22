/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4138 : Family 8 := level8.get ⟨139,by decide⟩
def sourceMap4138 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4138 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4138_checked : acceptsGraphIso
    (source (graph core4138) (root 8) 2 2) DegreeTwoThreeSpectrum3447.graph sourceMap4138=true := by decide +kernel
theorem fusedMap4138_checked : acceptsGraphIso
    (fused (graph core4138) (root 8) 2 2) DegreeTwoThreeSpectrum2676.graph fusedMap4138=true := by decide +kernel
theorem certified4138 : Certified (graph core4138) (root 8) 2 2 :=
  of_native_maps core4138 DegreeTwoThreeSpectrum3447.graph DegreeTwoThreeSpectrum2676.graph
    sourceMap4138 fusedMap4138 sourceMap4138_checked fusedMap4138_checked
    DegreeTwoThreeFiniteComparisons.comparison4138
#print axioms sourceMap4138_checked
#print axioms fusedMap4138_checked
#print axioms certified4138
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
