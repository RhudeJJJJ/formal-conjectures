/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5226 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap5226 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8,10,11,12,13,14,15] (sourceLabel 6 2 5 v)
def fusedMap5226 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 2 5 v)
theorem sourceMap5226_checked : acceptsGraphIso
    (source (graph core5226) (root 6) 2 5) DegreeTwoThreeSpectrum4153.graph sourceMap5226=true := by decide +kernel
theorem fusedMap5226_checked : acceptsGraphIso
    (fused (graph core5226) (root 6) 2 5) DegreeTwoThreeSpectrum3887.graph fusedMap5226=true := by decide +kernel
theorem certified5226 : Certified (graph core5226) (root 6) 2 5 :=
  of_native_maps core5226 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum3887.graph
    sourceMap5226 fusedMap5226 sourceMap5226_checked fusedMap5226_checked
    DegreeTwoThreeFiniteComparisons.comparison5226
#print axioms sourceMap5226_checked
#print axioms fusedMap5226_checked
#print axioms certified5226
def sourceMap5226swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,13,14,15,6,7,8] (sourceLabel 6 5 2 v)
def fusedMap5226swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 5 2 v)
theorem sourceMap5226swap_checked : acceptsGraphIso
    (source (graph core5226) (root 6) 5 2) DegreeTwoThreeSpectrum4153.graph sourceMap5226swap=true := by decide +kernel
theorem fusedMap5226swap_checked : acceptsGraphIso
    (fused (graph core5226) (root 6) 5 2) DegreeTwoThreeSpectrum3887.graph fusedMap5226swap=true := by decide +kernel
theorem certified5226swap : Certified (graph core5226) (root 6) 5 2 :=
  of_native_maps core5226 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum3887.graph
    sourceMap5226swap fusedMap5226swap sourceMap5226swap_checked fusedMap5226swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5226
#print axioms sourceMap5226swap_checked
#print axioms fusedMap5226swap_checked
#print axioms certified5226swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
