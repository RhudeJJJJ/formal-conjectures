/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4566 : Family 10 := level10.get ⟨489,by decide⟩
def sourceMap4566 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4566 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (fusedLabel 10 2 2 v)
theorem sourceMap4566_checked : acceptsGraphIso
    (source (graph core4566) (root 10) 2 2) DegreeTwoThreeSpectrum6347.graph sourceMap4566=true := by decide +kernel
theorem fusedMap4566_checked : acceptsGraphIso
    (fused (graph core4566) (root 10) 2 2) DegreeTwoThreeSpectrum5954.graph fusedMap4566=true := by decide +kernel
theorem certified4566 : Certified (graph core4566) (root 10) 2 2 :=
  of_native_maps core4566 DegreeTwoThreeSpectrum6347.graph DegreeTwoThreeSpectrum5954.graph
    sourceMap4566 fusedMap4566 sourceMap4566_checked fusedMap4566_checked
    DegreeTwoThreeFiniteComparisons.comparison4566
#print axioms sourceMap4566_checked
#print axioms fusedMap4566_checked
#print axioms certified4566
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
