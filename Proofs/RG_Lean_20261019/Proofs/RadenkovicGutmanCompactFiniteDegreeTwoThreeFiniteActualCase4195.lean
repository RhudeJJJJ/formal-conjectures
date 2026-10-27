/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4195 : Family 9 := level9.get ⟨22,by decide⟩
def sourceMap4195 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4195 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 2 2 v)
theorem sourceMap4195_checked : acceptsGraphIso
    (source (graph core4195) (root 9) 2 2) DegreeTwoThreeSpectrum4535.graph sourceMap4195=true := by decide +kernel
theorem fusedMap4195_checked : acceptsGraphIso
    (fused (graph core4195) (root 9) 2 2) DegreeTwoThreeSpectrum3868.graph fusedMap4195=true := by decide +kernel
theorem certified4195 : Certified (graph core4195) (root 9) 2 2 :=
  of_native_maps core4195 DegreeTwoThreeSpectrum4535.graph DegreeTwoThreeSpectrum3868.graph
    sourceMap4195 fusedMap4195 sourceMap4195_checked fusedMap4195_checked
    DegreeTwoThreeFiniteComparisons.comparison4195
#print axioms sourceMap4195_checked
#print axioms fusedMap4195_checked
#print axioms certified4195
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
