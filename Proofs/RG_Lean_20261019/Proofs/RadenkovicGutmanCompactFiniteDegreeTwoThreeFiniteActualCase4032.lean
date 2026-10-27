/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4032 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap4032 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,7,8,5,6,3,2,1,0,9,10,11,12,13,14,15] (sourceLabel 2 1 10 v)
def fusedMap4032 : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 1 10 v)
theorem sourceMap4032_checked : acceptsGraphIso
    (source (graph core4032) (root 2) 1 10) DegreeTwoThreeSpectrum3863.graph sourceMap4032=true := by decide +kernel
theorem fusedMap4032_checked : acceptsGraphIso
    (fused (graph core4032) (root 2) 1 10) DegreeTwoThreeSpectrum3861.graph fusedMap4032=true := by decide +kernel
theorem certified4032 : Certified (graph core4032) (root 2) 1 10 :=
  of_native_maps core4032 DegreeTwoThreeSpectrum3863.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap4032 fusedMap4032 sourceMap4032_checked fusedMap4032_checked
    DegreeTwoThreeFiniteComparisons.comparison4032
#print axioms sourceMap4032_checked
#print axioms fusedMap4032_checked
#print axioms certified4032
def sourceMap4032swap : (Vertices 2 ⊕ Fin 11 ⊕ Fin 2) → Fin 16 :=
  fun v => ![4,7,8,3,2,1,0,9,10,11,12,13,14,15,5,6] (sourceLabel 2 10 1 v)
def fusedMap4032swap : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 10 1 v)
theorem sourceMap4032swap_checked : acceptsGraphIso
    (source (graph core4032) (root 2) 10 1) DegreeTwoThreeSpectrum3863.graph sourceMap4032swap=true := by decide +kernel
theorem fusedMap4032swap_checked : acceptsGraphIso
    (fused (graph core4032) (root 2) 10 1) DegreeTwoThreeSpectrum3861.graph fusedMap4032swap=true := by decide +kernel
theorem certified4032swap : Certified (graph core4032) (root 2) 10 1 :=
  of_native_maps core4032 DegreeTwoThreeSpectrum3863.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap4032swap fusedMap4032swap sourceMap4032swap_checked fusedMap4032swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4032
#print axioms sourceMap4032swap_checked
#print axioms fusedMap4032swap_checked
#print axioms certified4032swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
