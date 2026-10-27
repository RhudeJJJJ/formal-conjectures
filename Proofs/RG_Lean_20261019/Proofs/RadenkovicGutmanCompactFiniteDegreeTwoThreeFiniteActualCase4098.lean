/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4098 : Family 8 := level8.get ⟨13,by decide⟩
def sourceMap4098 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,6,0,1,2,3,4,5,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4098 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 2 2 v)
theorem sourceMap4098_checked : acceptsGraphIso
    (source (graph core4098) (root 8) 2 2) DegreeTwoThreeSpectrum2627.graph sourceMap4098=true := by decide +kernel
theorem fusedMap4098_checked : acceptsGraphIso
    (fused (graph core4098) (root 8) 2 2) DegreeTwoThreeSpectrum2348.graph fusedMap4098=true := by decide +kernel
theorem certified4098 : Certified (graph core4098) (root 8) 2 2 :=
  of_native_maps core4098 DegreeTwoThreeSpectrum2627.graph DegreeTwoThreeSpectrum2348.graph
    sourceMap4098 fusedMap4098 sourceMap4098_checked fusedMap4098_checked
    DegreeTwoThreeFiniteComparisons.comparison4098
#print axioms sourceMap4098_checked
#print axioms fusedMap4098_checked
#print axioms certified4098
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
