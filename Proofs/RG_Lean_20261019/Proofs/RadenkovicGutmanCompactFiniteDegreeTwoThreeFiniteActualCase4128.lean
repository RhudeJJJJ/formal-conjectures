/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4128 : Family 8 := level8.get ⟨114,by decide⟩
def sourceMap4128 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4128 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4128_checked : acceptsGraphIso
    (source (graph core4128) (root 8) 2 2) DegreeTwoThreeSpectrum3229.graph sourceMap4128=true := by decide +kernel
theorem fusedMap4128_checked : acceptsGraphIso
    (fused (graph core4128) (root 8) 2 2) DegreeTwoThreeSpectrum2528.graph fusedMap4128=true := by decide +kernel
theorem certified4128 : Certified (graph core4128) (root 8) 2 2 :=
  of_native_maps core4128 DegreeTwoThreeSpectrum3229.graph DegreeTwoThreeSpectrum2528.graph
    sourceMap4128 fusedMap4128 sourceMap4128_checked fusedMap4128_checked
    DegreeTwoThreeFiniteComparisons.comparison4128
#print axioms sourceMap4128_checked
#print axioms fusedMap4128_checked
#print axioms certified4128
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
