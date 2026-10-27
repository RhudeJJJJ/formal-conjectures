/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons87
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4367 : Family 9 := level9.get ⟨514,by decide⟩
def sourceMap4367 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,7,8,9,1,2,3,4,5,6] (sourceLabel 9 2 2 v)
def fusedMap4367 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4367_checked : acceptsGraphIso
    (source (graph core4367) (root 9) 2 2) DegreeTwoThreeSpectrum4870.graph sourceMap4367=true := by decide +kernel
theorem fusedMap4367_checked : acceptsGraphIso
    (fused (graph core4367) (root 9) 2 2) DegreeTwoThreeSpectrum4602.graph fusedMap4367=true := by decide +kernel
theorem certified4367 : Certified (graph core4367) (root 9) 2 2 :=
  of_native_maps core4367 DegreeTwoThreeSpectrum4870.graph DegreeTwoThreeSpectrum4602.graph
    sourceMap4367 fusedMap4367 sourceMap4367_checked fusedMap4367_checked
    DegreeTwoThreeFiniteComparisons.comparison4367
#print axioms sourceMap4367_checked
#print axioms fusedMap4367_checked
#print axioms certified4367
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
