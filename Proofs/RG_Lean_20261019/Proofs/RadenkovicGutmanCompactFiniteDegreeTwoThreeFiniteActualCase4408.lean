/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4408 : Family 9 := level9.get ⟨611,by decide⟩
def sourceMap4408 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,12,13,14,15,6,7,8,9,10,11] (sourceLabel 9 2 2 v)
def fusedMap4408 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4408_checked : acceptsGraphIso
    (source (graph core4408) (root 9) 2 2) DegreeTwoThreeSpectrum4935.graph sourceMap4408=true := by decide +kernel
theorem fusedMap4408_checked : acceptsGraphIso
    (fused (graph core4408) (root 9) 2 2) DegreeTwoThreeSpectrum4307.graph fusedMap4408=true := by decide +kernel
theorem certified4408 : Certified (graph core4408) (root 9) 2 2 :=
  of_native_maps core4408 DegreeTwoThreeSpectrum4935.graph DegreeTwoThreeSpectrum4307.graph
    sourceMap4408 fusedMap4408 sourceMap4408_checked fusedMap4408_checked
    DegreeTwoThreeFiniteComparisons.comparison4408
#print axioms sourceMap4408_checked
#print axioms fusedMap4408_checked
#print axioms certified4408
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
