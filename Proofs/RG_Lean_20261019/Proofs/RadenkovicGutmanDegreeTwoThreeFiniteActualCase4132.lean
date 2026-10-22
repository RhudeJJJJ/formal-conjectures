/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4132 : Family 8 := level8.get ⟨125,by decide⟩
def sourceMap4132 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4132 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4132_checked : acceptsGraphIso
    (source (graph core4132) (root 8) 2 2) DegreeTwoThreeSpectrum3330.graph sourceMap4132=true := by decide +kernel
theorem fusedMap4132_checked : acceptsGraphIso
    (fused (graph core4132) (root 8) 2 2) DegreeTwoThreeSpectrum2582.graph fusedMap4132=true := by decide +kernel
theorem certified4132 : Certified (graph core4132) (root 8) 2 2 :=
  of_native_maps core4132 DegreeTwoThreeSpectrum3330.graph DegreeTwoThreeSpectrum2582.graph
    sourceMap4132 fusedMap4132 sourceMap4132_checked fusedMap4132_checked
    DegreeTwoThreeFiniteComparisons.comparison4132
#print axioms sourceMap4132_checked
#print axioms fusedMap4132_checked
#print axioms certified4132
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
