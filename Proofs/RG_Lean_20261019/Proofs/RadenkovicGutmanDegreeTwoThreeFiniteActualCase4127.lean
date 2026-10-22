/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4127 : Family 8 := level8.get ⟨111,by decide⟩
def sourceMap4127 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4127 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4127_checked : acceptsGraphIso
    (source (graph core4127) (root 8) 2 2) DegreeTwoThreeSpectrum3199.graph sourceMap4127=true := by decide +kernel
theorem fusedMap4127_checked : acceptsGraphIso
    (fused (graph core4127) (root 8) 2 2) DegreeTwoThreeSpectrum2516.graph fusedMap4127=true := by decide +kernel
theorem certified4127 : Certified (graph core4127) (root 8) 2 2 :=
  of_native_maps core4127 DegreeTwoThreeSpectrum3199.graph DegreeTwoThreeSpectrum2516.graph
    sourceMap4127 fusedMap4127 sourceMap4127_checked fusedMap4127_checked
    DegreeTwoThreeFiniteComparisons.comparison4127
#print axioms sourceMap4127_checked
#print axioms fusedMap4127_checked
#print axioms certified4127
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
