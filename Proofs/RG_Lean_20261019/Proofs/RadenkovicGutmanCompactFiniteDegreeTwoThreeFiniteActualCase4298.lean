/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4298 : Family 9 := level9.get ⟨348,by decide⟩
def sourceMap4298 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4298 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4298_checked : acceptsGraphIso
    (source (graph core4298) (root 9) 2 2) DegreeTwoThreeSpectrum4716.graph sourceMap4298=true := by decide +kernel
theorem fusedMap4298_checked : acceptsGraphIso
    (fused (graph core4298) (root 9) 2 2) DegreeTwoThreeSpectrum4247.graph fusedMap4298=true := by decide +kernel
theorem certified4298 : Certified (graph core4298) (root 9) 2 2 :=
  of_native_maps core4298 DegreeTwoThreeSpectrum4716.graph DegreeTwoThreeSpectrum4247.graph
    sourceMap4298 fusedMap4298 sourceMap4298_checked fusedMap4298_checked
    DegreeTwoThreeFiniteComparisons.comparison4298
#print axioms sourceMap4298_checked
#print axioms fusedMap4298_checked
#print axioms certified4298
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
