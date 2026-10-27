/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4125 : Family 8 := level8.get ⟨105,by decide⟩
def sourceMap4125 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4125 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4125_checked : acceptsGraphIso
    (source (graph core4125) (root 8) 2 2) DegreeTwoThreeSpectrum3137.graph sourceMap4125=true := by decide +kernel
theorem fusedMap4125_checked : acceptsGraphIso
    (fused (graph core4125) (root 8) 2 2) DegreeTwoThreeSpectrum2482.graph fusedMap4125=true := by decide +kernel
theorem certified4125 : Certified (graph core4125) (root 8) 2 2 :=
  of_native_maps core4125 DegreeTwoThreeSpectrum3137.graph DegreeTwoThreeSpectrum2482.graph
    sourceMap4125 fusedMap4125 sourceMap4125_checked fusedMap4125_checked
    DegreeTwoThreeFiniteComparisons.comparison4125
#print axioms sourceMap4125_checked
#print axioms fusedMap4125_checked
#print axioms certified4125
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
