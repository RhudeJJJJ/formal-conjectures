/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4167 : Family 8 := level8.get ⟨208,by decide⟩
def sourceMap4167 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4167 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4167_checked : acceptsGraphIso
    (source (graph core4167) (root 8) 2 2) DegreeTwoThreeSpectrum3786.graph sourceMap4167=true := by decide +kernel
theorem fusedMap4167_checked : acceptsGraphIso
    (fused (graph core4167) (root 8) 2 2) DegreeTwoThreeSpectrum2503.graph fusedMap4167=true := by decide +kernel
theorem certified4167 : Certified (graph core4167) (root 8) 2 2 :=
  of_native_maps core4167 DegreeTwoThreeSpectrum3786.graph DegreeTwoThreeSpectrum2503.graph
    sourceMap4167 fusedMap4167 sourceMap4167_checked fusedMap4167_checked
    DegreeTwoThreeFiniteComparisons.comparison4167
#print axioms sourceMap4167_checked
#print axioms fusedMap4167_checked
#print axioms certified4167
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
