/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4181 : Family 8 := level8.get ⟨237,by decide⟩
def sourceMap4181 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,12,13,14,6,7,8,9,10,11] (sourceLabel 8 2 2 v)
def fusedMap4181 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4181_checked : acceptsGraphIso
    (source (graph core4181) (root 8) 2 2) DegreeTwoThreeSpectrum3833.graph sourceMap4181=true := by decide +kernel
theorem fusedMap4181_checked : acceptsGraphIso
    (fused (graph core4181) (root 8) 2 2) DegreeTwoThreeSpectrum2662.graph fusedMap4181=true := by decide +kernel
theorem certified4181 : Certified (graph core4181) (root 8) 2 2 :=
  of_native_maps core4181 DegreeTwoThreeSpectrum3833.graph DegreeTwoThreeSpectrum2662.graph
    sourceMap4181 fusedMap4181 sourceMap4181_checked fusedMap4181_checked
    DegreeTwoThreeFiniteComparisons.comparison4181
#print axioms sourceMap4181_checked
#print axioms fusedMap4181_checked
#print axioms certified4181
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
