/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4334 : Family 9 := level9.get ⟨440,by decide⟩
def sourceMap4334 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4334 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4334_checked : acceptsGraphIso
    (source (graph core4334) (root 9) 2 2) DegreeTwoThreeSpectrum4816.graph sourceMap4334=true := by decide +kernel
theorem fusedMap4334_checked : acceptsGraphIso
    (fused (graph core4334) (root 9) 2 2) DegreeTwoThreeSpectrum4444.graph fusedMap4334=true := by decide +kernel
theorem certified4334 : Certified (graph core4334) (root 9) 2 2 :=
  of_native_maps core4334 DegreeTwoThreeSpectrum4816.graph DegreeTwoThreeSpectrum4444.graph
    sourceMap4334 fusedMap4334 sourceMap4334_checked fusedMap4334_checked
    DegreeTwoThreeFiniteComparisons.comparison4334
#print axioms sourceMap4334_checked
#print axioms fusedMap4334_checked
#print axioms certified4334
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
