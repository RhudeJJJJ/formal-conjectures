/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4100 : Family 8 := level8.get ⟨24,by decide⟩
def sourceMap4100 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap4100 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (fusedLabel 8 2 2 v)
theorem sourceMap4100_checked : acceptsGraphIso
    (source (graph core4100) (root 8) 2 2) DegreeTwoThreeSpectrum2817.graph sourceMap4100=true := by decide +kernel
theorem fusedMap4100_checked : acceptsGraphIso
    (fused (graph core4100) (root 8) 2 2) DegreeTwoThreeSpectrum2407.graph fusedMap4100=true := by decide +kernel
theorem certified4100 : Certified (graph core4100) (root 8) 2 2 :=
  of_native_maps core4100 DegreeTwoThreeSpectrum2817.graph DegreeTwoThreeSpectrum2407.graph
    sourceMap4100 fusedMap4100 sourceMap4100_checked fusedMap4100_checked
    DegreeTwoThreeFiniteComparisons.comparison4100
#print axioms sourceMap4100_checked
#print axioms fusedMap4100_checked
#print axioms certified4100
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
