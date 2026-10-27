/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4382 : Family 9 := level9.get ⟨555,by decide⟩
def sourceMap4382 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4382 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4382_checked : acceptsGraphIso
    (source (graph core4382) (root 9) 2 2) DegreeTwoThreeSpectrum4909.graph sourceMap4382=true := by decide +kernel
theorem fusedMap4382_checked : acceptsGraphIso
    (fused (graph core4382) (root 9) 2 2) DegreeTwoThreeSpectrum4188.graph fusedMap4382=true := by decide +kernel
theorem certified4382 : Certified (graph core4382) (root 9) 2 2 :=
  of_native_maps core4382 DegreeTwoThreeSpectrum4909.graph DegreeTwoThreeSpectrum4188.graph
    sourceMap4382 fusedMap4382 sourceMap4382_checked fusedMap4382_checked
    DegreeTwoThreeFiniteComparisons.comparison4382
#print axioms sourceMap4382_checked
#print axioms fusedMap4382_checked
#print axioms certified4382
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
