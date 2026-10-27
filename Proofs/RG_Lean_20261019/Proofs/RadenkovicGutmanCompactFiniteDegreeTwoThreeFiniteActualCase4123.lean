/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4123 : Family 8 := level8.get ⟨98,by decide⟩
def sourceMap4123 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4123 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4123_checked : acceptsGraphIso
    (source (graph core4123) (root 8) 2 2) DegreeTwoThreeSpectrum3053.graph sourceMap4123=true := by decide +kernel
theorem fusedMap4123_checked : acceptsGraphIso
    (fused (graph core4123) (root 8) 2 2) DegreeTwoThreeSpectrum2451.graph fusedMap4123=true := by decide +kernel
theorem certified4123 : Certified (graph core4123) (root 8) 2 2 :=
  of_native_maps core4123 DegreeTwoThreeSpectrum3053.graph DegreeTwoThreeSpectrum2451.graph
    sourceMap4123 fusedMap4123 sourceMap4123_checked fusedMap4123_checked
    DegreeTwoThreeFiniteComparisons.comparison4123
#print axioms sourceMap4123_checked
#print axioms fusedMap4123_checked
#print axioms certified4123
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
