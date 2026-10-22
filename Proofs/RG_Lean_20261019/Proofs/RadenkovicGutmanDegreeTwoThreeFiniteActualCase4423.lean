/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4423 : Family 9 := level9.get ⟨654,by decide⟩
def sourceMap4423 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4423 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4423_checked : acceptsGraphIso
    (source (graph core4423) (root 9) 2 2) DegreeTwoThreeSpectrum4950.graph sourceMap4423=true := by decide +kernel
theorem fusedMap4423_checked : acceptsGraphIso
    (fused (graph core4423) (root 9) 2 2) DegreeTwoThreeSpectrum4446.graph fusedMap4423=true := by decide +kernel
theorem certified4423 : Certified (graph core4423) (root 9) 2 2 :=
  of_native_maps core4423 DegreeTwoThreeSpectrum4950.graph DegreeTwoThreeSpectrum4446.graph
    sourceMap4423 fusedMap4423 sourceMap4423_checked fusedMap4423_checked
    DegreeTwoThreeFiniteComparisons.comparison4423
#print axioms sourceMap4423_checked
#print axioms fusedMap4423_checked
#print axioms certified4423
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
