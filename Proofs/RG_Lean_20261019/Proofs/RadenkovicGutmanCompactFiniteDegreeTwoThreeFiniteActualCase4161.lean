/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4161 : Family 8 := level8.get ⟨194,by decide⟩
def sourceMap4161 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4161 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4161_checked : acceptsGraphIso
    (source (graph core4161) (root 8) 2 2) DegreeTwoThreeSpectrum3758.graph sourceMap4161=true := by decide +kernel
theorem fusedMap4161_checked : acceptsGraphIso
    (fused (graph core4161) (root 8) 2 2) DegreeTwoThreeSpectrum2445.graph fusedMap4161=true := by decide +kernel
theorem certified4161 : Certified (graph core4161) (root 8) 2 2 :=
  of_native_maps core4161 DegreeTwoThreeSpectrum3758.graph DegreeTwoThreeSpectrum2445.graph
    sourceMap4161 fusedMap4161 sourceMap4161_checked fusedMap4161_checked
    DegreeTwoThreeFiniteComparisons.comparison4161
#print axioms sourceMap4161_checked
#print axioms fusedMap4161_checked
#print axioms certified4161
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
