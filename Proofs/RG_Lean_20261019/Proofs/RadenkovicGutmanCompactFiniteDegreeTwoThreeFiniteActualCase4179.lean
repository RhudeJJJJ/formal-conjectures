/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4179 : Family 8 := level8.get ⟨234,by decide⟩
def sourceMap4179 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4179 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4179_checked : acceptsGraphIso
    (source (graph core4179) (root 8) 2 2) DegreeTwoThreeSpectrum3828.graph sourceMap4179=true := by decide +kernel
theorem fusedMap4179_checked : acceptsGraphIso
    (fused (graph core4179) (root 8) 2 2) DegreeTwoThreeSpectrum2651.graph fusedMap4179=true := by decide +kernel
theorem certified4179 : Certified (graph core4179) (root 8) 2 2 :=
  of_native_maps core4179 DegreeTwoThreeSpectrum3828.graph DegreeTwoThreeSpectrum2651.graph
    sourceMap4179 fusedMap4179 sourceMap4179_checked fusedMap4179_checked
    DegreeTwoThreeFiniteComparisons.comparison4179
#print axioms sourceMap4179_checked
#print axioms fusedMap4179_checked
#print axioms certified4179
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
