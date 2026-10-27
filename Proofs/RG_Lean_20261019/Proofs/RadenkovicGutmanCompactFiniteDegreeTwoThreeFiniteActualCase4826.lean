/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4826 : Family 10 := level10.get ⟨1197,by decide⟩
def sourceMap4826 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4826 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4826_checked : acceptsGraphIso
    (source (graph core4826) (root 10) 2 2) DegreeTwoThreeSpectrum7284.graph sourceMap4826=true := by decide +kernel
theorem fusedMap4826_checked : acceptsGraphIso
    (fused (graph core4826) (root 10) 2 2) DegreeTwoThreeSpectrum6371.graph fusedMap4826=true := by decide +kernel
theorem certified4826 : Certified (graph core4826) (root 10) 2 2 :=
  of_native_maps core4826 DegreeTwoThreeSpectrum7284.graph DegreeTwoThreeSpectrum6371.graph
    sourceMap4826 fusedMap4826 sourceMap4826_checked fusedMap4826_checked
    DegreeTwoThreeFiniteComparisons.comparison4826
#print axioms sourceMap4826_checked
#print axioms fusedMap4826_checked
#print axioms certified4826
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
